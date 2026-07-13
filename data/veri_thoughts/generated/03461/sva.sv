module ripple_carry_adder_assertions(
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic Load,
    input logic Clear,
    input logic clock,
    input logic [3:0] S,
    input logic Cout
);

    // Clock: clock; reset: Clear (synchronous active high); logic is sequential.

    // After a clear cycle, both registered outputs are zero.
    check_clear_clears_outputs: assert property (
        @(posedge clock) disable iff (Clear || $initstate)
        $past(Clear) |-> ({Cout, S} == 5'b00000)
    );

    // Load captures A into S and Cin into Cout on the next cycle.
    check_load_captures_inputs: assert property (
        @(posedge clock) disable iff (Clear || $initstate)
        (!Clear && Load) |=> ({Cout, S} == {$past(Cin), $past(A)})
    );

    // With neither Clear nor Load asserted, the next cycle holds A + B + Cin.
    check_add_computes_result: assert property (
        @(posedge clock) disable iff (Clear || $initstate)
        (!Clear && !Load) |=> ({Cout, S} == ({1'b0, $past(A)} + {1'b0, $past(B)} + $past(Cin)))
    );

    // Clear has priority over Load when both were asserted in the prior cycle.
    check_clear_has_priority_over_load: assert property (
        @(posedge clock) disable iff (Clear || $initstate)
        $past(Clear && Load) |-> ({Cout, S} == 5'b00000)
    );

    // The registered outputs match the operation selected in the prior cycle.
    check_output_matches_selected_operation: assert property (
        @(posedge clock) disable iff (Clear || $initstate)
        ({Cout, S} == ($past(Clear) ? 5'b00000 :
                      ($past(Load) ? {$past(Cin), $past(A)} :
                                     ({1'b0, $past(A)} + {1'b0, $past(B)} + $past(Cin)))))
    );

endmodule