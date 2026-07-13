
module shift_register_32bit (
    input SHIFT,
    input DATA_IN,
    output SHIFT_OUT,
    output [31:0] DATA_OUT
);

reg [31:0] pipeline [0:2];

always @(posedge SHIFT) begin
    pipeline[0] <= {pipeline[0][30:0], DATA_IN};
    pipeline[1] <= pipeline[0];
    pipeline[2] <= pipeline[1];
end

assign DATA_OUT = pipeline[2];
assign SHIFT_OUT = pipeline[0][31];

endmodule
