mod cse;
mod cse_ip;
mod resolution;
mod skolem_normal_form;
mod unification;

fn main() {
  // コマンドライン引数からファイル名を取得
  let args: Vec<String> = std::env::args().collect();
  if args.len() < 2 {
    eprintln!("Usage: {} <tptp_file>", args[0]);
    std::process::exit(1);
  }

  let filename = &args[1];
  let cnf = skolem_normal_form::skolem_normal_form(filename);
  println!("{}", cnf);

  // println!("Resolution Result: {}\n", cnf.resolution());
  // println!("CSE Result: {}\n", cse::solve(&cnf));

  cse_ip::solve(&cnf);
}
