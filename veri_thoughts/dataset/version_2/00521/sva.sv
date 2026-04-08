module And_Module_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] out,
    input logic out_valid,
    input logic clk
);

    // out captures the bitwise AND of the prior-cycle inputs.
    check_out_registered_and: assert property (
        @(posedge clk) 1'b1 |=> (out == ($past(a) & $past(b)))
    );

    // out_valid is driven high after each clock edge.
    check_out_valid_asserted: assert property (
        @(posedge clk) 1'b1 |=> (out_valid == 1'b1)
    );

    // Once out_valid is high, it remains high on later clocks.
    check_out_valid_sticky_high: assert property (
        @(posedge clk) out_valid |=> out_valid
    );

    // Stable inputs across cycles keep the registered output stable.
    check_out_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b)) |=> $stable(out)
    );

    // A zero on either operand produces a zero output on the next cycle.
    check_zero_operand_forces_zero: assert property (
        @(posedge clk) ((a == 8'h00) || (b == 8'h00)) |=> (out == 8'h00)
    );

    // All ones on a passes b through to the next-cycle output.
    check_all_ones_a_passes_b: assert property (
        @(posedge clk) (a == 8'hFF) |=> (out == $past(b))
    );

    // All ones on b passes a through to the next-cycle output.
    check_all_ones_b_passes_a: assert property (
        @(posedge clk) (b == 8'hFF) |=> (out == $past(a))
    );

endmodule