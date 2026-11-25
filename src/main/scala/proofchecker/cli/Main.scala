package proofchecker.cli

@main def main(args: String*): Unit =
  val (code, message) = Cli.run(args.toList)
  if code == Cli.ExitOk then println(message) else System.err.println(message)
  sys.exit(code)
