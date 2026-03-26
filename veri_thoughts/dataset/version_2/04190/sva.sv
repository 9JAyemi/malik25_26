module MUX4to1_sva (
    input logic       clk,
    input logic [3:0] IN0,
    input logic [3:0] IN1,
    input logic [3:0] IN2,
    input logic [3:0] IN3,
    input logic [1:0] SEL,
    input logic       F
);

    // No clock or reset exists in the RTL; sample this combinational logic on clk.

    // SEL=00 routes IN0[0] to F.
    check_sel_00_routes_in0_lsb: assert property (
        @(posedge clk) (SEL === 2'b00) |-> (F === IN0[0])
    );

    // SEL=01 routes IN1[0] to F.
    check_sel_01_routes_in1_lsb: assert property (
        @(posedge clk) (SEL === 2'b01) |-> (F === IN1[0])
    );

    // SEL=10 routes IN2[0] to F.
    check_sel_10_routes_in2_lsb: assert property (
        @(posedge clk) (SEL === 2'b10) |-> (F === IN2[0])
    );

    // SEL=11 routes IN3[0] to F.
    check_sel_11_routes_in3_lsb: assert property (
        @(posedge clk) (SEL === 2'b11) |-> (F === IN3[0])
    );

endmodule