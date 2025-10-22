analyze -sv priority_encoder.v

elaborate -top priority_encoder

clock clk
# no reset signal exists in the RTL; define reset alias if needed
# reset reset


# Input one-hot or zero check
assert { $countones(I) <= 1 }

# Mapping checks: combinational mapping then one-clock register delay to output
# If I is one-hot for bit0..3, mapping should be 00,01,10,11 respectively.
assert { I == 4'b0001 |-> ##1 (O == 2'b00) }
assert { I == 4'b0010 |-> ##1 (O == 2'b01) }
assert { I == 4'b0100 |-> ##1 (O == 2'b10) }
assert { I == 4'b1000 |-> ##1 (O == 2'b11) }

# If I is zero or otherwise unmatched, RTL defaults to 2'b00 after one cycle
assert { I == 4'b0000 |-> ##1 (O == 2'b00) }

# Ensure O is stable during the clock half-cycle (no intra-cycle glitches)
assume {$past($rose(clk))} ;# ensure past available
assert { $rose(clk) |-> (O == $past(O)) }

# Optional: detect illegal multi-hot inputs by flagging when more than one bit set
assert { $countones(I) > 1 |-> ##0 (0) } ;# will fail when multi-hot occurs

# Set some proving options similar to vending script
set_prove_time_limit 3600
set_engine_mode Tri
prove -all
