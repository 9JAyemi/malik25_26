
module binary_search(
    input clk,
    input reset,
    input [31:0] target,
    input [31:0] data, // Change to packed array
    output reg found,
    output reg [4:0] index
);

    reg [4:0] low = 0;
    reg [4:0] high = 31;
    reg [4:0] mid;

    always @(posedge clk, posedge reset) begin
        if (reset) begin
            found <= 0;
            index <= -1;
            low <= 0;
            high <= 31;
        end else begin
            if (low > high) begin
                found <= 0;
                index <= -1;
            end else begin
                mid <= (low + high) / 2;
                if (data[mid] == target) begin
                    found <= 1;
                    index <= mid;
                end else if (data[mid] > target) begin
                    high <= mid - 1;
                end else begin
                    low <= mid + 1;
                end
            end
        end
    end

endmodule
