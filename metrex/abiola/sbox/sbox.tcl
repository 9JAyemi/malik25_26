analyze -sv sbox.v

elaborate -top sbox

clock clk
reset reset    ;# active-low reset in this RTL (assert triggers on !reset)

# Reset properties (active-low): on reset deassertion internals are cleared
assert { !reset |-> (to_invert == 4'b0000 && ah_reg == 4'b0000 && alph == 4'b0000) }

# Pipeline register update: on rising clock the registers take the "next_" values
assert { $rose(clk) |-> (to_invert == $past(next_to_invert) && ah_reg == $past(next_ah_reg) && alph == $past(next_alph)) }

# Combinational relation: next_alph is element-wise XOR of al and ah
assert { next_alph == (al ^ ah) }

# When decrypt_i is asserted (non-zero), output should be equal to the inverter's output (inva)
assert { decrypt_i != 0 |-> data_o == inva }

# Stability: data_o should not glitch within a clock half-cycle
assume {$past($rose(clk))} ;# ensure $past available
assert { $rose(clk) |-> (data_o == $past(data_o)) }

# Set prove options
set_prove_time_limit 3600
set_engine_mode Tri
prove -all
