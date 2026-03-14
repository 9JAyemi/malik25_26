
module binary_counter(
    input clk, reset, enable, load,
    input [3:0] in,
    output [3:0] out,
    output overflow
);

reg [3:0] counter;
reg [3:0] next_val;

assign overflow = (counter == 4'b1111);

always @(posedge clk) begin
    if (reset) begin
        counter <= 4'b0000;
    end else begin
        if (load) begin
            counter <= in;
        end else if (enable) begin
            counter <= counter + 4'b0001;
        end
    end
end

assign out = counter;

endmodule