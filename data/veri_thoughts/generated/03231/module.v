
module d_ff (
    output reg Q,
    output Q_N,
    input CLK,
    input D,
    input VPWR,
    input VGND,
    input VPB,
    input VNB
);

    assign Q_N = ~Q;

    // D Flip-Flop logic
    always @(posedge CLK) begin
        if (VPB == 0) begin // Set reset condition
            Q <= 0;
        end else begin
            Q <= D;     // Add explicit assignment delay
        end
    end

endmodule