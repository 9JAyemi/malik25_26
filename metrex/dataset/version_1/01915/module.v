
module controlrecorder(clock, reset, go, keys, countdown, mode, num_keys, cyclecounter, cell_number);

  input clock, reset, go;
  input [3:0] keys;
  input [25:0] countdown;
  output reg [1:0] mode;
  output reg [4:0] num_keys;
  output reg [25:0] cyclecounter;
  output reg [4:0] cell_number;

  reg [3:0] prev_keys;
  reg [2:0] current_state, next_state;
  reg [25:0] countdown_register;
  reg [31:0] keystrokes[0:30];
  integer i;

  localparam STATIONARY = 3'b000, 
             START_RECORD = 3'b001,
             RECORDING = 3'b010, 
             WAITING_FOR_PLAYBACK = 3'b011, 
             START_PLAYBACK = 3'b100, 
             PLAYBACK = 3'b101;

  always @(posedge clock) begin 
    if (!reset) begin 
      current_state <= STATIONARY;
      num_keys <= 5'b0;
      cyclecounter <= 26'b0;
      cell_number <= 5'b0;
    end 
    else begin 
      current_state <= next_state;
      case (current_state)
        STATIONARY: begin 
          if (go) begin 
            next_state <= START_RECORD;
          end 
          else begin 
            next_state <= STATIONARY;
          end 
        end 
        START_RECORD: begin 
          next_state <= RECORDING;
          cyclecounter <= 26'b0;
          num_keys <= 5'b0;
          cell_number <= 5'b0;
        end 
        RECORDING: begin 
          if (num_keys == 5'b11111) begin 
            next_state <= WAITING_FOR_PLAYBACK;
            cyclecounter <= 26'b0;
            cell_number <= 5'b0;
          end 
          else if (prev_keys != keys) begin 
            keystrokes[num_keys] <= keys;
            num_keys <= num_keys + 1'b1;
            cyclecounter <= 26'b0;
            cell_number <= cell_number + 1'b1;
          end 
          else if (cyclecounter == 26'b10111110101111000001111111) begin 
            cyclecounter <= 26'b0;
            cell_number <= cell_number + 1'b1;
          end 
          else begin 
            cyclecounter <= cyclecounter + 1'b1;
          end 
          next_state <= RECORDING;
        end 
        WAITING_FOR_PLAYBACK: begin 
          if (!go) begin 
            next_state <= START_PLAYBACK;
          end 
          else begin 
            next_state <= WAITING_FOR_PLAYBACK;
          end 
        end 
        START_PLAYBACK: begin 
          next_state <= PLAYBACK;
          countdown_register <= countdown;
          i <= 0;
          cell_number <= 5'b0;
        end 
        PLAYBACK: begin 
          if (countdown_register == 26'b0) begin 
            if (i == num_keys) begin 
              next_state <= STATIONARY;
            end
            else begin 
              prev_keys <= keystrokes[i];
              countdown_register <= countdown;
              i <= i + 1;
              cell_number <= cell_number + 1'b1;
            end 
          end 
          else begin 
            countdown_register <= countdown_register - 1'b1;
          end 
          next_state <= PLAYBACK;
        end 
      endcase 
    end 
  end 

  always @(*) begin 
    case (current_state)
      RECORDING: begin 
        mode <= 2'b01;
      end
      PLAYBACK: begin 
        mode <= 2'b10;
      end 
      default: begin 
        mode <= 2'b00;
      end 
    endcase 
  end 
endmodule