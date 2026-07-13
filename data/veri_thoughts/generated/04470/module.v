
module power_check (
    input  VPWR,
    input  VGND,
    input  VPB,
    input  VNB,
    output reg power_ok
);

    wire w_power_ok;

    assign w_power_ok = (VPWR && VPB);
    always @(*) begin
        power_ok <= w_power_ok;
    end

endmodule
