analyze -sv edge_detector.v

elaborate -top edge_detector

clock clk

# Check: when input changes (curr_in != prev_in) the FSM moves to state 3'b001
# We observe this as: change detected on combinational update of next_in/curr_in/prev_in
assert { (curr_in != prev_in) |-> ##1 (state == 3'b001) }

# Check: state progresses 001 -> 010 -> 011 -> (writes out and returns to 000)
assert { state == 3'b001 |-> ##1 (state == 3'b010) }
assert { state == 3'b010 |-> ##1 (state == 3'b011) }
assert { state == 3'b011 |-> ##1 (state == 3'b000) }

# Check: when state reaches 3'b011, out becomes next_in (captured input)
assert { state == 3'b011 |-> ##0 (out == next_in) }

# Check shift-register behavior: prev_in <= curr_in <= next_in <= in across posedges
assert { $rose(clk) |-> (prev_in == $past(curr_in) && curr_in == $past(next_in) && next_in == $past(in)) }

# Simple prover settings
set_prove_time_limit 3600
set_engine_mode Tri
prove -all
