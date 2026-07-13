module mux_4to1_enable_sva (
    input logic clk,
    input logic [7:0] D0,
    input logic [7:0] D1,
    input logic [7:0] D2,
    input logic [7:0] D3,
    input logic [1:0] SEL,
    input logic EN,
    input logic [7:0] Y
);

// When EN is low, Y must be zero.
    check_enable_low_clears_output: assert property (
        @(posedge clk) !EN |-> (Y == 8'h00)
    );

// When EN is high and SEL==00, Y equals D0.
    check_select_00_routes_d0: assert property (
        @(posedge clk) EN && (SEL == 2'b00) |-> (Y == D0)
    );

// When EN is high and SEL==01, Y equals D1.
    check_select_01_routes_d1: assert property (
        @(posedge clk) EN && (SEL == 2'b01) |-> (Y == D1)
    );

// When EN is high and SEL==10, Y equals D2.
    check_select_10_routes_d2: assert property (
        @(posedge clk) EN && (SEL == 2'b10) |-> (Y == D2)
    );

// When EN is high and SEL==11, Y equals D3.
    check_select_11_routes_d3: assert property (
        @(posedge clk) EN && (SEL == 2'b11) |-> (Y == D3)
    );

// Y equals the selected data input when EN is high.
    check_function_when_enabled: assert property (
        @(posedge clk) EN |-> (Y == (SEL == 2'b00 ? D0 :
                                     SEL == 2'b01 ? D1 :
                                     SEL == 2'b10 ? D2 : D3))
    );

// Y equals the selected data input when EN is high.
    check_function_when_enabled: assert property (
        @(posedge clk) EN |-> (Y == (SEL == 2'b00 ? D0 :
                                     SEL == 2'b01 ? D1 :
                                     SEL == 2'b10 ? D2 : D3))
    );

// Y equals the selected data input when EN is high.
    check_function_when_enabled: assert property (
        @(posedge clk) EN |-> (Y == (SEL == 2'b00 ? D0 :
                                     SEL == 2'b01 ? D1 :
                                     SEL == 2'b10 ? D2 : D3))
    );

// Y equals the selected data input when EN is high.
    check_function_when_enabled: assert property (
        @(posedge clk) EN |-> (Y == (SEL == 2'b00 ? D0 :
                                     SEL == 2'b01 ? D1 :
                                     SEL == 2'b10 ? D2 : D3))
    );

endmodule
