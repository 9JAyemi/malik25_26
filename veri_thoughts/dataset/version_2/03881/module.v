
module decoder (
    input [4:0] encode_in,
    output reg [31:0] data_out
);

integer i;

always @(*)
begin
    data_out = 0;
    data_out[1 << encode_in] = 1;
end

endmodule
