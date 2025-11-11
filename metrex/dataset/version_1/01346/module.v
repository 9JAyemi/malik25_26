module binary_display(
    input clk,
    input [3:0] data,
    output reg display_enable  
);

reg [3:0] prev_data;
reg [3:0] data_count;

always @(posedge clk) begin
    if (data == prev_data) begin
        data_count <= data_count + 1;
    end else begin
        data_count <= 0;
    end
    
    if (data_count == 9) begin
        display_enable <= 1;
        data_count <= 0;  
    end else begin
        display_enable <= (data_count == 0) ? 0 : display_enable;
    end
    
    prev_data <= data;
end

reg [3:0] count;  

always @(posedge clk) begin
    if (display_enable) begin
        count <= (count == 10) ? 0 : count + 1;
    end else begin
        count <= 0;  // Reset count when display_enable is not active
    end
end

endmodule
