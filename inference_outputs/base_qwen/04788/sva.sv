module sky130_fd_sc_lp__o31ai_sva (
    input logic Y,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);
    // No clock or reset signals are present in the RTL

    // Combinational logic: Y is driven by the output of a buffer
    // The buffer's input is the output of a NAND gate
    // The NAND gate's inputs are B1 and the output of an OR gate
    // The OR gate's inputs are A2, A1, and A3

    // The OR gate's output is always driven by the inputs A2, A1, and A3
    // The NAND gate's output is always driven by the inputs B1 and the OR gate's output
    // The buffer's output is always driven by the NAND gate's output

    // Since there are no clock or reset signals, we use combinational assertions
    // to check the behavior of the combinational logic

    // Y is always driven by the output of the buffer
    always_comb begin
        assert property (
            (Y == nand0_out)
        ) else $error("Y is not driven by the output of the buffer");
    end

    // The NAND gate's output is always driven by the inputs B1 and the OR gate's output
    always_comb begin
        assert property (
            (nand0_out == (B1 & or0_out))
        ) else $error("NAND gate's output is not driven by the inputs B1 and the OR gate's output");
    end

    // The OR gate's output is always driven by the inputs A2, A1, and A3
    always_comb begin
        assert property (
            (or0_out == (A2 | A1 | A3))
        ) else $error("OR gate's output is not driven by the inputs A2, A1, and A3");
    end
endmodule