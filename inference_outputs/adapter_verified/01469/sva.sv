module mux_sva (
    input logic clk,
    input logic [3:0] ABCD,
    input logic [1:0] SEL,
    input logic EN,
    input logic Y
);

// When EN is low, Y must be forced low.
    check_en_low_forces_zero: assert property (
        @(posedge clk) (EN == 1'b0) |-> (Y == 1'b0)
    );

// When EN is high and SEL==00, Y equals ABCD[0].
    check_sel00_routes_abcd0: assert property (
        @(posedge clk) (EN == 1'b1) && (SEL == 2'b00) |-> (Y == ABCD[0])
    );

// When EN is high and SEL==01, Y equals ABCD[1].
    check_sel01_routes_abcd1: assert property (
        @(posedge clk) (EN == 1'b1) && (SEL == 2'b01) |-> (Y == ABCD[1])
    );

// When EN is high and SEL==10, Y equals ABCD[2].
    check_sel10_routes_abcd2: assert property (
        @(posedge clk) (EN == 1'b1) && (SEL == 2'b10) |-> (Y == ABCD[2])
    );

// When EN is high and SEL==11, Y equals ABCD[3].
    check_sel11_routes_abcd3: assert property (
        @(posedge clk) (EN == 1'b1) && (SEL == 2'b11) |-> (Y == ABCD[3])
    );

endmodule
