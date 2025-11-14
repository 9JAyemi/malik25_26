
module sky130_fd_sc_hd__dlrtn_4 (
    Q,
    RESET_B,
    D,
    GATE_N
);

    output Q;
    input RESET_B;
    input D;
    input GATE_N;

    reg Q_int = 1'b0;
    reg D_ff = 1'b0;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB;
    supply0 VNB;

    // D flip-flop to store input value
    always @(posedge RESET_B) begin
        if (!RESET_B) begin
            D_ff <= 1'b0;
        end else begin
            D_ff <= D;
        end
    end

    // Mux to select output value
    always @(posedge RESET_B) begin
        if (!RESET_B) begin
            Q_int <= 1'b0;
        end else begin
            Q_int <= (GATE_N) ? D_ff : Q_int;
        end
    end

    assign Q = Q_int;

endmodule
module sky130_fd_sc_hd__dlrtn (
    Q,
    RESET_B,
    D,
    GATE_N
);

    output Q;
    input RESET_B;
    input [3:0] D;
    input GATE_N;

    reg [3:0] Q_int = 4'b0;
    reg [3:0] D_ff = 4'b0;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB;
    supply0 VNB;

    // D flip-flop to store input value
    always @(posedge RESET_B) begin
        if (!RESET_B) begin
            D_ff <= 4'b0;
        end else begin
            D_ff <= D;
        end
    end

    // Mux to select output value
    always @(posedge RESET_B) begin
        if (!RESET_B) begin
            Q_int <= 4'b0;
        end else begin
            Q_int <= (GATE_N) ? D_ff : Q_int;
        end
    end

    assign Q = Q_int[0];

endmodule