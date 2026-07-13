module adder8_sva (
    input  logic        CLK,
    input  logic [7:0]  a,
    input  logic [7:0]  b,
    input  logic        cin,
    input  logic [7:0]  sum,
    input  logic        cout
);
    ///// Functional arithmetic equivalence /////
    // Sum+carry equals 9-bit addition of inputs.
    check_add_result: assert property (
        @(posedge CLK) disable iff ($initstate)
        {cout, sum} == ({1'b0, a} + {1'b0, b} + cin)
    );

    // Carry-out equals MSB of 9-bit addition.
    check_cout_is_msb: assert property (
        @(posedge CLK) disable iff ($initstate)
        cout == ({1'b0, a} + {1'b0, b} + cin)[8]
    );

    // LSB sum equals a[0] XOR b[0] XOR cin.
    check_sum0_xor: assert property (
        @(posedge CLK) disable iff ($initstate)
        sum[0] == (a[0] ^ b[0] ^ cin)
    );

    ///// Special-case identities /////
    // Adding zero B and zero carry returns A with no carry.
    check_add_zero_b: assert property (
        @(posedge CLK) disable iff ($initstate)
        ((b == 8'h00) && (cin == 1'b0)) |-> ((sum == a) && (cout == 1'b0))
    );

    // Adding zero A and zero carry returns B with no carry.
    check_add_zero_a: assert property (
        @(posedge CLK) disable iff ($initstate)
        ((a == 8'h00) && (cin == 1'b0)) |-> ((sum == b) && (cout == 1'b0))
    );

    // A + ~A + 1 -> 0 with carry-out 1.
    check_complement_plus_one: assert property (
        @(posedge CLK) disable iff ($initstate)
        ((b == ~a) && (cin == 1'b1)) |-> ((sum == 8'h00) && (cout == 1'b1))
    );

    // A + ~A + 0 -> 0xFF with no carry-out.
    check_complement_no_carry: assert property (
        @(posedge CLK) disable iff ($initstate)
        ((b == ~a) && (cin == 1'b0)) |-> ((sum == 8'hFF) && (cout == 1'b0))
    );

    // 0xFF + 0 + 1 -> 0 with carry-out 1.
    check_ff_plus_one: assert property (
        @(posedge CLK) disable iff ($initstate)
        ((a == 8'hFF) && (b == 8'h00) && (cin == 1'b1)) |-> ((sum == 8'h00) && (cout == 1'b1))
    );

    ///// Temporal consistency (purely combinational determinism) /////
    // If inputs are stable, outputs remain stable.
    check_stable_outputs_when_inputs_stable: assert property (
        @(posedge CLK) disable iff ($initstate)
        ($stable(a) && $stable(b) && $stable(cin)) |-> ($stable(sum) && $stable(cout))
    );

    // With B and CIN stable, incrementing A by 1 increments the 9-bit result by 1.
    check_result_increments_when_a_increments: assert property (
        @(posedge CLK) disable iff ($initstate)
        ((a == $past(a) + 8'd1) && (b == $past(b)) && (cin == $past(cin)))
        |-> ({cout, sum} == ($past({cout, sum}) + 9'd1))
    );

    // With A and CIN stable, incrementing B by 1 increments the 9-bit result by 1.
    check_result_increments_when_b_increments: assert property (
        @(posedge CLK) disable iff ($initstate)
        ((b == $past(b) + 8'd1) && (a == $past(a)) && (cin == $past(cin)))
        |-> ({cout, sum} == ($past({cout, sum}) + 9'd1))
    );

    // When all inputs are zero, outputs are zero.
    check_all_zero: assert property (
        @(posedge CLK) disable iff ($initstate)
        ((a == 8'h00) && (b == 8'h00) && (cin == 1'b0)) |-> ((sum == 8'h00) && (cout == 1'b0))
    );
endmodule