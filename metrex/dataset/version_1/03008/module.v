
module binary_search (
    input wire clk,
    input wire reset,
    input wire start,
    input wire [31:0] array,
    input wire [7:0] array_len,
    input wire [31:0] target,
    output reg found,
    output reg [7:0] index
);

reg [31:0] low, high, mid;
reg [7:0] i;
reg done;

always @(posedge clk or negedge reset) begin
    if (!reset) begin
        low <= 0;
        high <= 0;
        mid <= 0;
        i <= 0;
        done <= 0;
    end else begin
        if (start && !done) begin
            low <= 0;
            high <= array_len - 1;
            done <= 0;
            i <= 0;
        end else if (i < array_len && !done) begin
            mid <= (low + high) / 2;
            if (array[mid] == target) begin
                found <= 1;
                index <= mid;
                done <= 1;
            end else if (array[mid] > target) begin
                high <= mid - 1;
            end else begin
                low <= mid + 1;
            end
            i <= i + 1;
        end else if (i >= array_len && !done) begin
            found <= 0;
            index <= -1;
            done <= 1;
        end
    end
end

endmodule
