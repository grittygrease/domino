// SPDX-License-Identifier: MIT OR Apache-2.0

//use crate::project::error::Result;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error("error parsing utf8: {0}")]
    Utf8Error(#[from] std::string::FromUtf8Error),
    #[error("io error: {0}")]
    IOError(#[from] std::io::Error),
    #[error("solver reply to (get-model) is complete but not a parsable model: {0}")]
    ModelUnparsable(String),
    #[error("solver output closed before a model was read: {0}")]
    ModelStreamClosed(String),
}

type Result<T> = std::result::Result<T, Error>;

use std::io::Read;
use std::io::Write as IOWrite;
use std::mem::swap;
use std::sync::mpsc::Sender;

use crate::util::{smtmodel::SmtModel, smtparser::parse_model};

pub struct Communicator {
    stdout: std::process::ChildStdout,
    chan: Option<std::sync::mpsc::Sender<String>>,
    thrd: Option<std::thread::JoinHandle<Result<()>>>,
    buf: Vec<u8>,
    pos: usize,
}

impl Communicator {
    pub fn new_from_cmd_without_transcript(cmd: std::process::Command) -> Result<Self> {
        Self::new_from_cmd::<Vec<u8>>(cmd, None)
    }

    pub fn new_from_cmd<W: std::io::Write + Send + Sync + 'static>(
        mut cmd: std::process::Command,
        mut transcript: Option<W>,
    ) -> Result<Self> {
        let mut cmd = cmd.spawn()?;

        let (send, recv) = std::sync::mpsc::channel();

        let mut stdin = cmd.stdin.take().unwrap();
        let stdout = cmd.stdout.take().unwrap();

        let thrd = std::thread::spawn(move || {
            writeln!(stdin)?;
            stdin.flush()?;
            if let Some(ref mut transcript) = transcript {
                writeln!(transcript)?;
                transcript.flush()?;
            }
            for data in recv {
                if let Some(ref mut transcript) = transcript {
                    write!(transcript, "{data}")?;
                    transcript.flush()?;
                }

                write!(stdin, "{data}")?;
                stdin.flush()?;
            }

            // Close stdin to make the smt solver terminate
            drop(stdin);

            // Wait and collect child process
            cmd.wait()?;
            Ok(())
        });

        let buf = vec![0u8; 1 << 10];

        Ok(Communicator {
            stdout,
            chan: Some(send),
            thrd: Some(thrd),
            buf,
            pos: 0,
        })
    }

    fn maybe_resize(&mut self) {
        if self.buf.len() - self.pos < self.buf.len() / 10 {
            self.buf.resize(self.buf.len() * 2, 0u8);
        }
    }

    pub fn read_until_pred<T, P: Fn(usize, &str) -> (usize, Option<T>)>(
        &mut self,
        p: P,
    ) -> Result<T> {
        loop {
            self.maybe_resize();
            let read_cnt = self.stdout.read(&mut self.buf[self.pos..])?;
            self.pos += read_cnt;

            let data = String::from_utf8(self.buf[..self.pos].to_vec())?;
            if let (data_read, Some(v)) = p(read_cnt, &data) {
                let rest_bs = &data.as_bytes()[data_read..];

                self.buf.fill(0);
                self.pos = rest_bs.len();
                self.buf[..self.pos].copy_from_slice(rest_bs);

                return Ok(v);
            }
        }
    }

    pub fn read_until(&mut self, pattern: &str) -> Result<(usize, String)> {
        loop {
            self.maybe_resize();
            self.pos += self.stdout.read(&mut self.buf[self.pos..])?;
            let data = String::from_utf8(self.buf[..self.pos].to_vec())?;

            if let Some(match_start) = data.find(pattern) {
                let match_end = match_start + pattern.len();

                let ret = data[..match_end].to_string();
                let rest_bs = &data.as_bytes()[match_end..];

                self.buf.fill(0);
                self.pos = rest_bs.len();
                self.buf[..self.pos].copy_from_slice(rest_bs);

                return Ok((match_start, ret));
            }
        }
    }

    /// Reads one model. A reply that is a complete expression but not a parsable model is an
    /// error, as is end of output, so reading the model of a failed claim cannot block.
    pub fn read_model(&mut self) -> Result<(usize, String, SmtModel)> {
        loop {
            self.maybe_resize();
            let read_cnt = self.stdout.read(&mut self.buf[self.pos..])?;
            self.pos += read_cnt;
            let data = String::from_utf8(self.buf[..self.pos].to_vec())?;

            if let Ok((model, cnt)) = parse_model(&data) {
                let modelstring = data[..cnt].to_string();

                let rest_bs = &data.as_bytes()[cnt..];

                self.buf.fill(0);
                self.pos = rest_bs.len();
                self.buf[..self.pos].copy_from_slice(rest_bs);

                return Ok((cnt, modelstring, model));
            }
            if holds_complete_expression(&data) {
                return Err(Error::ModelUnparsable(data));
            }
            if read_cnt == 0 {
                return Err(Error::ModelStreamClosed(data));
            }
        }
    }

    pub fn read_until_end(&mut self) -> Result<String> {
        let mut data = String::from_utf8(self.buf[..self.pos].to_vec())?;
        self.stdout.read_to_string(&mut data)?;
        Ok(data)
    }

    pub fn close(&mut self) {
        let mut none = None;
        swap(&mut self.chan, &mut none)
    }

    pub fn join(&mut self) -> Result<()> {
        if self.thrd.is_none() {
            return Ok(());
        }

        let mut thrd = None;
        swap(&mut thrd, &mut self.thrd);

        thrd.unwrap().join().expect("error joining thread")
    }

    pub fn child_is_finished(&self) -> bool {
        if let Some(thrd) = &self.thrd {
            thrd.is_finished()
        } else {
            // this is only None if we have already joined
            true
        }
    }
}

impl std::fmt::Write for Communicator {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        if self.child_is_finished() {
            if let Err(e) = self.join() {
                log::error!("client finished with a error {e}. last output:");
                std::io::copy(&mut self.stdout, &mut std::io::stderr()).unwrap();
                std::io::stderr().flush().expect("error flushing stderr");

                return Err(std::fmt::Error);
            }
        }

        let chan: &Sender<String> = self.chan.as_ref().expect("writing to closed communicator");

        if chan.send(s.to_string()).is_err() {
            // this means the prover process has quit.
            // it's time to join our thread to get the actual error.

            let thread_result = self.join();
            let rest = self.read_until_end().unwrap();

            log::error!("result from prover communication thread:\n  {thread_result:?}");
            log::error!("rest of data from prover:\n  {rest}");
            std::io::stderr().flush().expect("error flushing stderr");

            Err(std::fmt::Error)
        } else {
            Ok(())
        }
    }
}

/// Whether `data` begins with one complete parenthesized expression. Parentheses inside
/// string literals and quoted symbols do not count.
fn holds_complete_expression(data: &str) -> bool {
    let mut depth = 0usize;
    let mut in_string = false;
    let mut in_quoted = false;
    for c in data.chars() {
        match c {
            '"' if !in_quoted => in_string = !in_string,
            '|' if !in_string => in_quoted = !in_quoted,
            '(' if !in_string && !in_quoted => depth += 1,
            ')' if !in_string && !in_quoted => {
                if depth <= 1 {
                    return true;
                }
                depth -= 1;
            }
            _ => {}
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cat_communicator(input: &str) -> Communicator {
        let mut cmd = std::process::Command::new("printf");
        cmd.arg("%s")
            .arg(input)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped());
        Communicator::new_from_cmd_without_transcript(cmd).expect("spawn printf")
    }

    #[test]
    fn complete_expression_detection() {
        assert!(!holds_complete_expression(""));
        assert!(!holds_complete_expression("(model (define-fun a () Int"));
        assert!(holds_complete_expression("(error \"no model)\")\n"));
        assert!(!holds_complete_expression("(error \"no model)"));
        assert!(holds_complete_expression("(|a)b| 1)"));
        assert!(holds_complete_expression("((define-fun a () Int 1))"));
    }

    #[test]
    fn complete_unparsable_reply_is_an_error_not_a_hang() {
        let mut comm = cat_communicator("((define-fun a () (_ BitVec 3) #o7))\n");
        let got = comm.read_model();
        assert!(
            matches!(got, Err(Error::ModelUnparsable(_))),
            "{:?}",
            got.map(|r| r.1)
        );
    }

    #[test]
    fn closed_output_is_an_error_not_a_hang() {
        let mut comm = cat_communicator("(model (define-fun a () Int");
        assert!(matches!(
            comm.read_model(),
            Err(Error::ModelStreamClosed(_))
        ));
    }
}
