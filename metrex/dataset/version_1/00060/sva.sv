// SVA for four_or_gate: concise, race-safe, and with focused coverage/checks

module four_or_gate_sva (
    input logic in1,
    input logic in2,
    input logic in3,
    input logic in4,
    input logic out
);

    // Functional equivalence (race-safe on any relevant change)
    property p_or_correct;
        @(in1 or in2 or in3 or in4 or out)
            1'b1 |-> ##0 (out === (in1 | in2 | in3 | in4));
    endproperty
    assert property (p_or_correct);

    // Known inputs imply known output (no X/Z leakage when inputs are 0/1)
    property p_known_inputs_imply_known_out;
        @(in1 or in2 or in3 or in4 or out)
            !($isunknown({in1,in2,in3,in4})) |-> ##0 !($isunknown(out));
    endproperty
    assert property (p_known_inputs_imply_known_out);

    // Sanity: single-input control of output when others are 0
    assert property (@(in1 or in2 or in3 or in4 or out)
                     (!in2 && !in3 && !in4 && $rose(in1)) |-> ##0 out);
    assert property (@(in1 or in2 or in3 or in4 or out)
                     (!in1 && !in3 && !in4 && $rose(in2)) |-> ##0 out);
    assert property (@(in1 or in2 or in3 or in4 or out)
                     (!in1 && !in2 && !in4 && $rose(in3)) |-> ##0 out);
    assert property (@(in1 or in2 or in3 or in4 or out)
                     (!in1 && !in2 && !in3 && $rose(in4)) |-> ##0 out);

    assert property (@(in1 or in2 or in3 or in4 or out)
                     (!in2 && !in3 && !in4 && $fell(in1)) |-> ##0 !out);
    assert property (@(in1 or in2 or in3 or in4 or out)
                     (!in1 && !in3 && !in4 && $fell(in2)) |-> ##0 !out);
    assert property (@(in1 or in2 or in3 or in4 or out)
                     (!in1 && !in2 && !in4 && $fell(in3)) |-> ##0 !out);
    assert property (@(in1 or in2 or in3 or in4 or out)
                     (!in1 && !in2 && !in3 && $fell(in4)) |-> ##0 !out);

    // Coverage: all-low case, each single-high case, multi-high case, and out edges
    cover property (@(in1 or in2 or in3 or in4 or out)
                    ##0 (!in1 && !in2 && !in3 && !in4 && !out));
    cover property (@(in1 or in2 or in3 or in4 or out)
                    ##0 ( in1 && !in2 && !in3 && !in4 &&  out));
    cover property (@(in1 or in2 or in3 or in4 or out)
                    ##0 (!in1 &&  in2 && !in3 && !in4 &&  out));
    cover property (@(in1 or in2 or in3 or in4 or out)
                    ##0 (!in1 && !in2 &&  in3 && !in4 &&  out));
    cover property (@(in1 or in2 or in3 or in4 or out)
                    ##0 (!in1 && !in2 && !in3 &&  in4 &&  out));
    cover property (@(in1 or in2 or in3 or in4 or out)
                    ##0 ((|{in1,in2,in3,in4}) && !$onehot0({in1,in2,in3,in4}) && out));

    cover property (@(in1 or in2 or in3 or in4 or out) $rose(out));
    cover property (@(in1 or in2 or in3 or in4 or out) $fell(out));

endmodule

// Bind into the DUT
bind four_or_gate four_or_gate_sva u_four_or_gate_sva (
    .in1(in1), .in2(in2), .in3(in3), .in4(in4), .out(out)
);