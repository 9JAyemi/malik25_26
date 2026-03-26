
module delay_element(
    input A,
    input VPWR,
    input VGND,
    input VPB,
    input VNB,
    output reg X
);

reg [31:0] count = 0;

always @(posedge VPWR)
begin
    if (count == 500)
        X <= A;
    else
        count <= count + 1;
end

endmodule