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

    // When disabled, the output is forced to zero.
    check_output_zero_when_disabled: assert property (
        @(posedge clk) !EN |-> (Y == 8'b0)
    );

    // When enabled and SEL selects D0, the output matches D0.
    check_select_d0_when_enabled: assert property (
        @(posedge clk) (EN && (SEL == 2'b00)) |-> (Y == D0)
    );

    // When enabled and SEL selects D1, the output matches D1.
    check_select_d1_when_enabled: assert property (
        @(posedge clk) (EN && (SEL == 2'b01)) |-> (Y == D1)
    );

    // When enabled and SEL selects D2, the output matches D2.
    check_select_d2_when_enabled: assert property (
        @(posedge clk) (EN && (SEL == 2'b10)) |-> (Y == D2)
    );

    // When enabled and SEL selects D3, the output matches D3.
    check_select_d3_when_enabled: assert property (
        @(posedge clk) (EN && (SEL == 2'b11)) |-> (Y == D3)
    );

endmodule