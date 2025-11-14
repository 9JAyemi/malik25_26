module top_module (
    input clk,
    input [7:0] d,
    output [7:0] q
);

reg [2:0] counter;
reg [7:0] dff_data;

always @(negedge clk) begin
    counter <= (counter == 3'b111) ? 3'b000 : counter + 3'b001;
    if (counter == 3'b111) begin
        dff_data <= 8'b00000000;
    end else begin
        dff_data <= {dff_data[6:0], d[7]};
    end
end

assign q = dff_data;

endmodule