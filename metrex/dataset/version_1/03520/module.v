
module fifo_memory(
    input clk,
    input wr_en,
    input rd_en,
    input [7:0] data_in,
    output reg empty,
    output reg full,
    output reg [7:0] data_out
);

    parameter SIZE = 8;
    reg [7:0] memory [SIZE-1:0];
    reg [2:0] head, tail;
    reg [2:0] next_tail;
    reg [2:0] next_head;
    
    always @(posedge clk) begin
        if(wr_en && !full) begin
            memory[tail] <= data_in;
            tail <= next_tail;
        end
    end
    
    always @(posedge clk) begin
        if(rd_en && !empty) begin
            data_out <= memory[head];
            head <= next_head;
        end
    end
    
    always @(*) begin
        next_tail = (tail + 1) % SIZE;
        next_head = (head + 1) % SIZE;
        empty = (head == tail) ? 1'b1 : 1'b0;
        full = ((next_tail == head) && (head != tail)) ? 1'b1 : 1'b0;
    end
    
endmodule