module m1_sva (
    input  logic        clk,
    input  logic [3:0]  a,
    input  logic [3:0]  b
);
    // When a <= 4, b equals a<<1 (4-bit wrap)
    check_le4_double: assert property (
        @(posedge clk) (a <= 4'd4) |-> (b == {a[2:0], 1'b0})
    );

    // When a > 4, b equals a>>1
    check_gt4_half: assert property (
        @(posedge clk) (a > 4'd4) |-> (b == (a >> 1))
    );

    // LSB is 0 on doubling path
    check_le4_lsb_zero: assert property (
        @(posedge clk) (a <= 4'd4) |-> (b[0] == 1'b0)
    );

    // MSB is 0 on halving path
    check_gt4_msb_zero: assert property (
        @(posedge clk) (a > 4'd4) |-> (b[3] == 1'b0)
    );

    // Corner: a==0 maps to b==0
    check_zero_map: assert property (
        @(posedge clk) (a == 4'd0) |-> (b == 4'd0)
    );

    // Corner: a==4 maps to b==8
    check_four_map: assert property (
        @(posedge clk) (a == 4'd4) |-> (b == 4'd8)
    );

    // Corner: a==5 maps to b==2
    check_five_map: assert property (
        @(posedge clk) (a == 4'd5) |-> (b == 4'd2)
    );

    // Corner: a==15 maps to b==7
    check_fifteen_map: assert property (
        @(posedge clk) (a == 4'd15) |-> (b == 4'd7)
    );

    // On halving path, LSB of b equals a[1]
    check_gt4_lsb_bit: assert property (
        @(posedge clk) (a > 4'd4) |-> (b[0] == a[1])
    );

    // If a is stable, b is stable (purely combinational)
    check_stable_mapping: assert property (
        @(posedge clk) $stable(a) |-> $stable(b)
    );
endmodule