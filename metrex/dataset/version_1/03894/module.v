module tri_intersect_data_array(
    reset,
    clk,
    address0,
    ce0,
    we0,
    d0,
    q0,
    address1,
    ce1,
    we1,
    d1,
    q1);

parameter DataWidth = 32'd576;
parameter AddressRange = 32'd20;
parameter AddressWidth = 32'd5;

input reset;
input clk;
input[AddressWidth - 1:0] address0;
input ce0;
input we0;
input[DataWidth - 1:0] d0;
output[DataWidth - 1:0] q0;
input[AddressWidth - 1:0] address1;
input ce1;
input we1;
input[DataWidth - 1:0] d1;
output[DataWidth - 1:0] q1;

reg [DataWidth-1:0] tri_intersect_array [0:AddressRange-1];

integer i;

always @(posedge clk or posedge reset) begin
    if (reset) begin
        for (i = 0; i < AddressRange; i = i + 1) begin
            tri_intersect_array[i] <= 0;
        end
    end else if (ce0 && we0) begin
        tri_intersect_array[address0] <= d0;
    end else if (ce1 && we1) begin
        tri_intersect_array[address1] <= d1;
    end
end

assign q0 = tri_intersect_array[address0] & tri_intersect_array[address1];
assign q1 = tri_intersect_array[address0] & tri_intersect_array[address1];

endmodule