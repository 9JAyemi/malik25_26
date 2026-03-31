```systemverilog
module mux_4to1_enable_sva (
    input logic CLK,
    input logic EN,
    input logic [1:0] SEL,
    input logic [7:0] D0,
    input logic [7:0] D1,
    input logic [7:0] D2,
    input logic [7:0] D3,
    output logic [7:0] Y
);
    // Mux output is 0 when EN is 0
    mux_output_zero: assert property (
        @(posedge CLK) disable iff (!EN) (Y == 8'b0)
    );

    // Mux output is one of the inputs when EN is 1
    mux_output_valid: assert property (
        @(posedge CLK) disable iff (!EN) (Y == D0 || Y == D1 || Y == D2 || Y == D3)
    );

    // Mux output is one of the inputs corresponding to SEL
    mux_output_correct: assert property (
        @(posedge CLK) disable iff (!EN) (SEL == 2'b00) |-> (Y == D0) ||
                                      (SEL == 2'b01) |-> (Y == D1) ||
                                      (SEL == 2'b10) |-> (Y == D2) ||
                                      (SEL == 2'b11) |-> (Y == D3)
    );
endmodule
```