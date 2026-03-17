module top_module_sva (
    input logic        clk,
    input logic [3:0]  DIN,
    input logic [1:0]  SHIFT,
    input logic [3:0]  a,
    input logic [3:0]  b,
    input logic        cin,
    input logic        cout,
    input logic [3:0]  sum,
    input logic [3:0]  DOUT
);

    // SHIFT=00 selects DIN[0], DIN[0], DIN[3], DIN[2] into the first adder.
    check_first_stage_shift_00: assert property (
        @(posedge clk)
        (SHIFT == 2'b00) |-> ({cout, DOUT} == ({1'b0, a} + {1'b0, {DIN[0], DIN[0], DIN[3], DIN[2]}} + cin))
    );

    // SHIFT=01 selects DIN[0], DIN[1], DIN[3], DIN[2] into the first adder.
    check_first_stage_shift_01: assert property (
        @(posedge clk)
        (SHIFT == 2'b01) |-> ({cout, DOUT} == ({1'b0, a} + {1'b0, {DIN[0], DIN[1], DIN[3], DIN[2]}} + cin))
    );

    // SHIFT=10 selects DIN[1], DIN[0], DIN[3], DIN[2] into the first adder.
    check_first_stage_shift_10: assert property (
        @(posedge clk)
        (SHIFT == 2'b10) |-> ({cout, DOUT} == ({1'b0, a} + {1'b0, {DIN[1], DIN[0], DIN[3], DIN[2]}} + cin))
    );

    // SHIFT=11 selects DIN[1], DIN[1], DIN[3], DIN[2] into the first adder.
    check_first_stage_shift_11: assert property (
        @(posedge clk)
        (SHIFT == 2'b11) |-> ({cout, DOUT} == ({1'b0, a} + {1'b0, {DIN[1], DIN[1], DIN[3], DIN[2]}} + cin))
    );

    // sum is DOUT plus b plus cin, truncated to 4 bits.
    check_sum_from_dout_b_cin: assert property (
        @(posedge clk)
        ({1'b0, sum} == (({1'b0, DOUT} + {1'b0, b} + cin) & 5'h0f))
    );

    // DOUT and cout do not depend on b.
    check_first_stage_independent_of_b: assert property (
        @(posedge clk)
        ($stable(DIN) && $stable(SHIFT) && $stable(a) && $stable(cin)) |-> ($stable(DOUT) && $stable(cout))
    );

    // sum depends only on DOUT, b, and cin.
    check_sum_stable_when_inputs_stable: assert property (
        @(posedge clk)
        ($stable(DOUT) && $stable(b) && $stable(cin)) |-> $stable(sum)
    );

    // With b and cin both zero, sum matches DOUT.
    check_sum_equals_dout_when_b_and_cin_zero: assert property (
        @(posedge clk)
        ((b == 4'h0) && (cin == 1'b0)) |-> (sum == DOUT)
    );

    // All outputs remain stable when all inputs remain stable.
    check_outputs_stable_when_all_inputs_stable: assert property (
        @(posedge clk)
        ($stable(DIN) && $stable(SHIFT) && $stable(a) && $stable(b) && $stable(cin)) |-> ($stable(cout) && $stable(sum) && $stable(DOUT))
    );

endmodule