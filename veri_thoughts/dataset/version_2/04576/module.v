
module d_latch_reset (
    input  wire        D,
    input  wire        GATE_N,
    input  wire        RESET_B,
    output reg         Q
);

    // Voltage supply signals
    supply1 VDD;
    supply0 VGND;

    always @ (posedge GATE_N) begin
        if (RESET_B == 0) begin
            Q <= 0;
        end else begin
            Q <= D;
        end
    end

endmodule
