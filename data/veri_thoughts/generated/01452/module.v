
module my_module (
    Q,
    CLK,
    D,
    SCD,
    SCE,
    RESET_B,
    VPWR,
    VGND,
    VPB,
    VNB
);

    // Module ports
    output Q;
    input CLK;
    input D;
    input SCD;
    input SCE;
    input RESET_B;
    input VPWR;
    input VGND;
    input VPB;
    input VNB;

    // Local signals
    wire buf_Q;
    wire RESET;
    wire mux_out;
    reg notifier;
    wire D_delayed;
    wire SCD_delayed;
    wire SCE_delayed;
    wire RESET_B_delayed;
    wire CLK_delayed;
    wire awake;
    wire cond0;
    wire cond1;
    wire cond2;
    wire cond3;
    wire cond4;

    // Inverters
    not (RESET, RESET_B_delayed);

    // Multiplexer
    mux2_1 mux0 (mux_out, D_delayed, SCD_delayed, SCE_delayed);

    // D Flip-Flop
    dff dff0 (buf_Q, mux_out, CLK_delayed, RESET, notifier);

    // Power & Ground
    assign awake = (VPWR === 1'b1);

    // Combinational Logic
    assign cond0 = ((RESET_B_delayed === 1'b1) && awake);
    assign cond1 = ((SCE_delayed === 1'b0) && cond0);
    assign cond2 = ((SCE_delayed === 1'b1) && cond0);
    assign cond3 = ((D_delayed !== SCD_delayed) && cond0);
    assign cond4 = ((RESET_B === 1'b1) && awake);

    // Output buffer
    buf buf0 (Q, buf_Q);

    // Delayed signals
    buf dlclkbuf0 (D_delayed, D, CLK, RESET_B);
    buf dlclkbuf1 (SCD_delayed, SCD, CLK, RESET_B);
    buf dlclkbuf2 (SCE_delayed, SCE, CLK, RESET_B);
    buf dlclkbuf3 (RESET_B_delayed, RESET_B, CLK, RESET_B);
    buf dlclkbuf4 (CLK_delayed, CLK, CLK, RESET_B);

    // Notifier
    always @(posedge CLK) begin
        if (cond1 || cond2 || cond3 || cond4) begin
            notifier <= 1'b1;
        end else begin
            notifier <= 1'b0;
        end
    end

endmodule

module mux2_1 (out, in0, in1, sel);
    parameter WIDTH=1;

    input [WIDTH-1:0] in0, in1;
    input sel;

    output [WIDTH-1:0] out;

    assign out = (sel) ? in1 : in0;
endmodule

module dff (Q, D, CLK, RST, notifier);

    parameter WIDTH=1;

    input [WIDTH-1:0] D;
    input CLK, RST;
    input notifier;

    output [WIDTH-1:0] Q;

    reg [WIDTH-1:0] Q_reg;
    wire RSTB;

    not RST_inv(RSTB, RST);

    always @(posedge CLK or negedge RSTB) begin
        if (~RSTB)
            Q_reg <= {WIDTH{1'b0}};
        else if (notifier)
            Q_reg <= D;
    end

    assign Q = Q_reg;

endmodule
