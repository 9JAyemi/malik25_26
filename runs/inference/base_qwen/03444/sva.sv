module Multiplexer_AC__parameterized36_sva (
    input logic CLK,
    input logic [1:0] ctrl,
    input logic [0:0] D0,
    input logic [0:0] D1,
    input logic [0:0] D2,
    input logic [0:0] D3,
    input logic [0:0] S
);
    // The multiplexer selects one of the four inputs based on the control signal.
    // The output should be one of the inputs D0, D1, D2, or D3, or 'x' if the control signal is invalid.
    mux_output: assert property (
        @(posedge CLK) disable iff (!CLK) (ctrl == 2'b00) |-> (S == D0)
    );
    mux_output_1: assert property (
        @(posedge CLK) disable iff (!CLK) (ctrl == 2'b01) |-> (S == D1)
    );
    mux_output_2: assert property (
        @(posedge CLK) disable iff (!CLK) (ctrl == 2'b10) |-> (S == D2)
    );
    mux_output_3: assert property (
        @(posedge CLK) disable iff (!CLK) (ctrl == 2'b11) |-> (S == D3)
    );
    mux_output_invalid: assert property (
        @(posedge CLK) disable iff (!CLK) (ctrl != 2'b00 && ctrl != 2'b01 && ctrl != 2'b10 && ctrl != 2'b11) |-> (S == 1'bx)
    );
endmodule