module data_flip_flop (
    output reg Q,
    input CLK,
    input D
);

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB;
    supply0 VNB;

    always @(posedge CLK) begin
        Q <= D;
    end

endmodule