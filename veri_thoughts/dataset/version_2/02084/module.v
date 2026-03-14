
module d_latch(
    input wire D,
    input wire NOTIFIER,
    input wire VPWR,
    input wire VGND,
    input wire GATE,
    output reg Q
);

reg Q_next;

initial begin
    Q = 1'bx;
end

always @(posedge GATE) begin
    if (NOTIFIER) begin
        Q_next = D;
    end else begin
        Q_next = Q;
    end
end

always @* begin
    if (VPWR) begin
        Q_next = 1'b1;
    end else if (VGND) begin
        Q_next = 1'b0;
    end
end

always @(posedge GATE) begin
    if (VPWR) begin
        Q <= 1'b1;
    end else if (VGND) begin
        Q <= 1'b0;
    end else if (NOTIFIER) begin
        Q <= D;
    end
end

endmodule