
module shift_register (
    input CLK,
    input SI,
    output SO,
    output [3:0] Q
);

reg [3:0] pipeline_reg;

always @(posedge CLK) begin
    if (SI) begin
        pipeline_reg <= 1'b1;
    end else begin
        pipeline_reg <= {pipeline_reg[2:0], SO};
    end
end

assign Q = pipeline_reg;
assign SO = pipeline_reg[0];

endmodule
