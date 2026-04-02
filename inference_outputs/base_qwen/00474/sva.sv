module XOR_M_assertions (
    input logic CLK,
    input logic Sgn_X,
    input logic Sgn_Y,
    input logic Sgn_Info
);
    // XOR logic must be correct
    xor_logic: assert property (
        @(posedge CLK) disable iff (!CLK) Sgn_Info == (Sgn_X ^ Sgn_Y)
    );
endmodule