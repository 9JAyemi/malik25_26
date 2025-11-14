

module delay_30_degrees
(
    input               clk_i,
    input               rst_i,
    input       [31:0]  offset_i,   input       [2:0]   position_i, output reg  [2:0]   position_o  );

localparam MAX_SPEED_COUNT  = 32'h1000000;
localparam RESET            = 6'b000001;
localparam INIT             = 6'b000010;
localparam CHANGE_POSITION  = 6'b000100;
localparam DELAY_30_DEGREES = 6'b001000;
localparam APPLY_CHANGE     = 6'b010000;
localparam IDLE             = 6'b100000;
reg [5:0]   state         = RESET;  reg [5:0]   next_state    = RESET;  reg [2:0]   position_old  = 3'h0;   reg [31:0]  speed_count   = 32'h0;  reg [31:0]  speed_divider = 32'h0;  reg [31:0]  delay_count   = 32'h0;  always @*
begin
    next_state = state;

    case (state)
        RESET:
        begin
            next_state = INIT;
        end
        INIT:
        begin
            if (position_i != position_old)
            begin
                next_state = CHANGE_POSITION;
            end
        end
        CHANGE_POSITION:
        begin
            next_state = DELAY_30_DEGREES;
        end
        DELAY_30_DEGREES:
        begin
            if( delay_count >  speed_divider)
            begin
                next_state          = APPLY_CHANGE;
            end
        end
        APPLY_CHANGE:
        begin
            next_state          = IDLE;
        end
        IDLE:
        begin
            if (position_i != position_old)
            begin
                next_state = CHANGE_POSITION;
            end
        end
        default:
        begin
            next_state = RESET;
        end
    endcase
end

always @(posedge clk_i)
begin
    case(state)
        RESET:
        begin
            speed_count     <= 0;
            speed_divider   <= 0;
            position_o      <= 3'b1;
        end
        INIT:
        begin
            if (speed_count < MAX_SPEED_COUNT)
            begin
                speed_count <= speed_count + 1;
            end
        end
        CHANGE_POSITION:
        begin
            speed_divider   <= speed_count >> 1 ;
            speed_count     <= 0;
            delay_count     <= 0;
        end
        DELAY_30_DEGREES:
        begin
            if (speed_count < MAX_SPEED_COUNT)
            begin
                speed_count <= speed_count + 1;
            end
            delay_count <= delay_count + 1;
        end
        APPLY_CHANGE:
        begin
            if (position_i == 3'b101)
            begin
                position_o <= 100;
            end 
            if (position_i == 3'b100)
            begin
                position_o <= 110;
            end 
            if (position_i == 3'b110)
            begin
                position_o <= 010;
            end 
            if (position_i == 3'b010)
            begin
                position_o <= 011;
            end 
            if (position_i == 3'b011)
            begin
                position_o <= 001;
            end 
            if (position_i == 3'b001)
            begin
                position_o <= 101;
            end 
            position_old    <= position_i;
            if (speed_count < MAX_SPEED_COUNT)
            begin
                speed_count <= speed_count + 1;
            end
        end
        IDLE:
        begin
            if (speed_count < MAX_SPEED_COUNT)
            begin
                speed_count <= speed_count + 1;
            end
        end
    endcase
end

always @ (posedge clk_i)
begin
    if(rst_i == 1'b1)
    begin
        state <= RESET;
    end
    else
    begin
        state <= next_state;
    end
end

endmodule

