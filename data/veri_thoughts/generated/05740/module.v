module logic_circuit (
    input Q,
    input CLK,
    input D,
    input SCD,
    input SCE,
    output reg Q_out
);

    wire mux_out;
    wire D_delayed;
    wire SCD_delayed;
    wire SCE_delayed;

    // Assuming the mux selects between D and SCD based on SCE
    assign mux_out = SCE ? SCD : D;

    // Simple D Flip-Flop functionality with additional logic for SCE and SCD
    always @(posedge CLK) begin
        if (SCE == 1'b0) begin
            Q_out <= D; // Direct path when SCE is low
        end else if (SCE == 1'b1) begin
            Q_out <= mux_out; // Mux output when SCE is high
        end
    end

endmodule
