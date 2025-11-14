module deserializer #(
        parameter   WIDTH = 8
    )(
        input                   rxd,
        input                   rst,
        input                   clk,
        output [WIDTH - 1:0]    data,
        output                  received
    );
    localparam s0 = 2'b00;
    localparam s1 = 2'b01;
    localparam s2 = 2'b11;
    localparam s3 = 2'b10;
    
    reg [1:0]           state           = s0;
    reg [7:0]           bit_index       = 0;
    reg [WIDTH - 1:0]   data_buf        = 0;
    reg                 received_buf    = 0;
    
    assign              data = data_buf;
    assign              received = received_buf;
    
    always@(posedge clk)
    begin
        if(rst)
        begin
            state = s0;
            bit_index = 0;
            data_buf = 0;
            received_buf = 0;
        end
        else
        begin
            case(state)
            s0:
            begin
                if(rxd)
                begin
                    state = s1;
                    bit_index = 0;
                end
            end
            s1:
            begin
                if(bit_index < WIDTH)
                begin
                    data_buf[bit_index] = rxd;
                    bit_index = bit_index + 1;
                end
                else
                begin
                    state = s2;
                    received_buf = 1;
                end
            end
            s2:
            begin
                state = s3;
            end
            s3:
            begin
                state = s0;
                bit_index = 0;
                data_buf = 0;
                received_buf = 0;
            end
            endcase
        end
    end
endmodule