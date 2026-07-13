
module dff_pipeline(
    input clk,
    input clr,
    input d,
    output q
);

reg [2:0] dff;

always @(posedge clk, negedge clr) begin
    if (~clr) begin
        dff <= 3'b111;
    end else begin
        dff <= {dff[1:0], d};
    end
end

assign q = dff[2];

endmodule