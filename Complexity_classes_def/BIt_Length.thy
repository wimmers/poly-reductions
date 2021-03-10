theory Bit_Length 
  begin

fun bit_length::"nat \<Rightarrow> nat" where 
"bit_length  0 = 0" | 
"bit_length  n = 1 + bit_length (n div 2) "

end