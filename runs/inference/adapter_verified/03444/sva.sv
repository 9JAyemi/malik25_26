module Multiplexer_AC__parameterized36_sva (
    input logic clk,
    input logic [1:0] ctrl,
    input logic [0:0] D0,
    input logic [0:0] D1,
    input logic [0:0] D2,
    input logic [0:0] D3,
    input logic [0:0] S
);

// S must match the RTL mux expression.
    check_mux_function: assert property (
        @(posedge clk) S == ((ctrl == 2'b00) ? D0 :
                             (ctrl == 2'b01) ? D1 :
                             (ctrl == 2'b10) ? D2 :
                             (ctrl == 2'b11) ? D3 :
                             1'bx)
    );

// ctrl==00 selects D0.
    check_select_00: assert property (
        @(posedge clk) (ctrl == 2'b00) |-> (S == D0)
    );

// ctrl==01 selects D1.
    check_select_01: assert property (
        @(posedge clk) (ctrl == 2'b01) |-> (S == D1)
    );

// ctrl==10 selects D2.
    check_select_10: assert property (
        @(posedge clk) (ctrl == 2'b10) |-> (S == D2)
    );

// ctrl==11 selects D3.
    check_select_11: assert property (
        @(posedge clk) (ctrl == 2'b11) |-> (S == D3)
    );

// Any ctrl value other than 00/01/10/11 drives S to x.
    check_default_x: assert property (
        @(posedge clk) !((ctrl == 2'b00) || (ctrl == 2'b01) || (ctrl == 2'b10) || (ctrl == 2'b11)) |-> (S == 1'bx)
    );

endmodule
