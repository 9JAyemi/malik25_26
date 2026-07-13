module dff_with_set (
    output Q,
    input D,
    input CLK,
    input SET,
    input NOTIFIER,
    input VPWR,
    input VGND
);

reg Q;

always @ (posedge CLK or negedge SET) begin
    if (!SET) begin
        Q <= 1'b0;
    end else begin
        Q <= D;
    end
end

assign NOTIFIER = (Q != D);

endmodule