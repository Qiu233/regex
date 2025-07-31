import Regex

open Regex

#eval regex%[ab|c|2|3]
#eval regex%[[a-zA-Z_0-9]]
#eval regex%[[^a-zA-Z_0-9]]
#eval regex%[[ \f\n\r\t\v]]
#eval regex%[[^ \f\n\r\t\v]]
#eval regex%[[0-9]]
#eval regex%[[^0-9]]

#eval regex%[(a(bc))(d|a)|(\d{3,4})].match "abcaabcd12345"

def main : IO Unit := pure ()
