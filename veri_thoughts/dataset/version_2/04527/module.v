module DFFAR (input D, input CLK, input RST, output Q, output QN);

reg Qtemp;

assign QN = ~Qtemp;
assign Q = Qtemp;

always @(posedge CLK or negedge RST) begin
    if (!RST) begin
        Qtemp <= 1'b0;
    end else begin
        Qtemp <= D;
    end
end

endmodule