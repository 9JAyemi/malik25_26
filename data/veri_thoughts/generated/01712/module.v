module dff_ctrl (
    output reg Q,
    input D,
    input CLK,
    input SET,
    input SLEEP_B,
    input NOTIFIER,
    input KAPWR,
    input VGND,
    input VPWR
);

    reg Q_int;
    wire KAPWR_int;
    wire VGND_int;
    wire VPWR_int;

    assign KAPWR_int = ~KAPWR;
    assign VGND_int = ~VGND;
    assign VPWR_int = ~VPWR;

    always @(posedge CLK or negedge SET)
    begin
        if (SET == 1'b0)
            Q <= 1'b0;
        else
            Q <= D;
    end

    always @*
    begin
        Q_int = NOTIFIER ? ~Q : Q;
    end

endmodule