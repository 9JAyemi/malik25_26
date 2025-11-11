

module GrayCounter
   #(parameter   COUNTER_WIDTH = 4)
   
    (output reg  [COUNTER_WIDTH-1:0]    gray_count_out,  input wire                         en,  input wire                         rst,   input wire                         clk);

    reg    [COUNTER_WIDTH-1:0]         binary_count;

    always @ (posedge clk)
        if (rst) begin
            binary_count   <= {COUNTER_WIDTH{1'b 0}} + 1;  gray_count_out <= {COUNTER_WIDTH{1'b 0}};      end
        else if (en) begin
            binary_count   <= binary_count + 1;
            gray_count_out <= {binary_count[COUNTER_WIDTH-1],
                              binary_count[COUNTER_WIDTH-2:0] ^ binary_count[COUNTER_WIDTH-1:1]};
        end
    
endmodule
