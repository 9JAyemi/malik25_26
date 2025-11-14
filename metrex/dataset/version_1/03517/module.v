
module fifo_buffer(
    input clock,
    input ready,
    input [7:0] head,

    input tail_req, //RTL
    input tail_ack,
    input [7:0] tail_value,
    input tail_value_valid,

    input req,
    output reg ack,
    output reg [7:0] value,
    output reg value_valid
);

reg [7:0] buffer [0:255];
reg [7:0] read_pointer;
reg [7:0] write_pointer;
reg write_data;
reg [7:0] write_pointer_next;
reg [7:0] read_pointer_next;
reg [7:0] read_data;
reg [7:0] tail_data;
reg [7:0] tail_pointer;
reg [7:0] tail_pointer_next;
reg [7:0] head_pointer;
reg [7:0] head_pointer_next;
reg [7:0] buffer_size;
reg [7:0] buffer_size_next;
reg tail_full;
reg head_full;
reg tail_empty;
reg head_empty;

always @(posedge clock) begin

    if (ready) begin

        // Write data to the head
        if (!head_full && head_pointer == write_pointer) begin
            buffer[write_pointer] <= head;
            write_pointer_next <= write_pointer + 1;
            if (write_pointer_next == 256) begin
                write_pointer_next <= 0;
            end
            head_full <= (write_pointer_next == read_pointer);
        end else begin
            write_pointer_next <= write_pointer;
            head_full <= 0;
        end

        // Read data from the head
        if (req && !head_empty && read_pointer == head_pointer) begin
            read_data <= buffer[read_pointer];
            read_pointer_next <= read_pointer + 1;
            if (read_pointer_next == 256) begin
                read_pointer_next <= 0;
            end
            head_empty <= (read_pointer_next == write_pointer);
        end else begin
            read_pointer_next <= read_pointer;
            head_empty <= 1;
        end

        // Write data to the tail
        if (!tail_full && tail_pointer == write_pointer && tail_req) begin
            buffer[tail_pointer] <= tail_data;
            tail_pointer_next <= tail_pointer - 1;
            if (tail_pointer_next == -1) begin
                tail_pointer_next <= 255;
            end
            tail_full <= (tail_pointer_next == write_pointer);
        end else begin
            tail_pointer_next <= tail_pointer;
            tail_full <= 0;
        end

        // Read data from the tail
        if (tail_value_valid && !tail_empty && tail_pointer == read_pointer) begin
            tail_data <= tail_value;
            tail_pointer_next <= tail_pointer - 1;
            if (tail_pointer_next == -1) begin
                tail_pointer_next <= 255;
            end
            tail_empty <= (tail_pointer_next == write_pointer);
        end else begin
            tail_pointer_next <= tail_pointer;
            tail_empty <= 1;
        end

        // Update buffer size
        if (head_pointer <= tail_pointer) begin
            buffer_size_next <= tail_pointer - head_pointer;
        end else begin
            buffer_size_next <= 256 - head_pointer + tail_pointer;
        end

        // Update head pointer
        if (!head_empty) begin
            head_pointer_next <= read_pointer_next;
        end else begin
            head_pointer_next <= head_pointer;
        end

        // Update tail pointer
        if (!tail_full && tail_req) begin
            tail_pointer_next <= tail_pointer_next;
        end else begin
            tail_pointer_next <= tail_pointer;
        end

    end else begin
        write_pointer_next <= write_pointer;
        read_pointer_next <= read_pointer;
        head_pointer_next <= head_pointer;
        tail_pointer_next <= tail_pointer;
        tail_data <= tail_data;
        buffer_size_next <= buffer_size;
    end
end

always @(*) begin
    write_pointer <= write_pointer_next;
    read_pointer <= read_pointer_next;
    head_pointer <= head_pointer_next;
    tail_pointer <= tail_pointer_next;
    buffer_size <= buffer_size_next;

    if (!head_empty && head_pointer == read_pointer) begin
        value <= read_data;
        ack <= tail_ack ; //Fix
        value_valid <= tail_value_valid;
    end else begin
        value <= 0;
        ack <= 0;
        value_valid <= 0;
    end

end

endmodule