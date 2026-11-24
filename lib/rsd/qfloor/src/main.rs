//! Canonical SCM Expr q only. Evaluation remains the frozen Lean evalLF.
#![allow(dead_code)]
mod ast;
mod content_hash;
mod json;
mod sha256;
mod wire;
use std::io::{self, BufRead, Write};

fn line(input: &str) -> json::Json {
    let decoded = json::parse(input)
        .and_then(|j| wire::decode_expr(j.get("expr").unwrap_or(&j)));
    match decoded {
        Ok(expr) => json::obj(vec![
            ("ok", json::Json::Bool(true)),
            ("q", json::Json::Str(content_hash::content_hash(&expr))),
        ]),
        Err(error) => wire::error_envelope(&error),
    }
}

fn serve() -> Result<(), String> {
    let input = io::stdin();
    let mut output = io::stdout().lock();
    for text in input.lock().lines() {
        let text = text.map_err(|e| format!("nf_scm_q_read: {e}"))?;
        let result = json::to_string(&line(&text));
        writeln!(output, "{result}").and_then(|_| output.flush())
            .map_err(|e| format!("nf_scm_q_write: {e}"))?;
    }
    Ok(())
}

fn main() {
    let result = std::thread::Builder::new().stack_size(64 * 1024 * 1024)
        .spawn(serve).map_err(|e| format!("nf_scm_q_thread: {e}"))
        .and_then(|thread| thread.join()
            .map_err(|_| "nf_scm_q_worker_terminated".to_owned()))
        .and_then(|result| result);
    if let Err(error) = result {
        eprintln!("{error}");
        std::process::exit(2);
    }
}
