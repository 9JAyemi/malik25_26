module sky130_fd_sc_hs__dlygate4sd2 (
    input A,
    input VPWR,
    input VGND,
    output reg X
);

reg [3:0] delay_count;

always @(posedge VPWR or negedge VGND)
begin
    if (VGND == 1'b0)
        X <= 1'b0;
    else if (A == 1'b1)
    begin
        delay_count <= 4'b1111;
        X <= 1'b0;
    end
    else if (delay_count != 0)
        delay_count <= delay_count - 1;
    else
        X <= 1'b1;
end

endmodule