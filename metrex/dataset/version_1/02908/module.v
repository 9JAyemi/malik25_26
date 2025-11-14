
module arbitro (

  input wire [2:0] pe_request_bundle,
    input wire [2:0] north_request_bundle,
    input wire [2:0] east_request_bundle,

output reg [1:0] pe_cfg_bundle,
    output reg [2:0] south_cfg_bundle,
    output reg [2:0] west_cfg_bundle,

output reg      r2pe_ack
  );

localparam  MUX_EAST  = 3'b111;
  localparam  MUX_NORTH = 3'b101;
  localparam  MUX_PE    = 3'b001;
  localparam  MUX_NULL  = 3'b000;
  localparam  PE_NULL   = 2'b00;

wire [2:0] request_vector;

  assign request_vector = {east_request_bundle[0], north_request_bundle[0], pe_request_bundle[0]};

always @(*)
  begin

  west_cfg_bundle  = MUX_NULL;
  south_cfg_bundle = MUX_NULL;
  pe_cfg_bundle    = PE_NULL;

  r2pe_ack         = 1'b0;

    case (request_vector)
      3'b000: begin
          end


      3'b001: begin
          r2pe_ack = 1'b1;
          case (pe_request_bundle[2:1])
            2'b00:  west_cfg_bundle  = MUX_PE;    2'b01:  west_cfg_bundle  = MUX_PE;    2'b10:  south_cfg_bundle = MUX_PE;    2'b11:
              begin
                r2pe_ack = 1'b0;
                south_cfg_bundle = MUX_NULL;  end
          endcase
        end


      3'b010: case (north_request_bundle[2:1])
          2'b00:  west_cfg_bundle  = MUX_NORTH; 2'b01:  west_cfg_bundle  = MUX_NORTH; 2'b10:  south_cfg_bundle = MUX_NORTH; 2'b11:  pe_cfg_bundle    = 2'b01;     endcase


      3'b011: begin
          r2pe_ack = 1'b1;
          case (north_request_bundle[2:1])
              2'b00:
                begin
                  west_cfg_bundle  = MUX_NORTH; south_cfg_bundle = MUX_PE;    end
            2'b01:
              begin
                west_cfg_bundle  = MUX_NORTH; south_cfg_bundle = MUX_PE;    end
            2'b10:
              begin
                south_cfg_bundle = MUX_NORTH; west_cfg_bundle  = MUX_PE;    end
            2'b11:
              begin
                west_cfg_bundle = MUX_PE;    pe_cfg_bundle   = 2'b01;     end
          endcase
        end


      3'b100: case (east_request_bundle[2:1])
          2'b00:  west_cfg_bundle  = MUX_EAST; 2'b01:  west_cfg_bundle  = MUX_EAST; 2'b10:  south_cfg_bundle = MUX_EAST; 2'b11:  pe_cfg_bundle    = 2'b11;  endcase


      3'b101: begin
          r2pe_ack = 1'b1;
          case (east_request_bundle[2:1])
            2'b00:
              begin
                west_cfg_bundle  = MUX_EAST; south_cfg_bundle = MUX_PE;   end

            2'b01:
              begin
                west_cfg_bundle  = MUX_EAST; south_cfg_bundle = MUX_PE;   end
            2'b10:
              begin
                south_cfg_bundle = MUX_EAST; west_cfg_bundle  = MUX_PE;   end
            2'b11:
              begin
                west_cfg_bundle = MUX_PE;  pe_cfg_bundle   = 2'b11;   end
          endcase
        end


      3'b110: case (east_request_bundle[2:1])
          2'b00:
            begin
              west_cfg_bundle  = MUX_EAST;  south_cfg_bundle = MUX_NORTH; end

          2'b01:
            begin
              west_cfg_bundle  = MUX_EAST;  south_cfg_bundle = MUX_NORTH; end
          2'b10:
            begin
              south_cfg_bundle = MUX_EAST;  west_cfg_bundle  = MUX_NORTH; end
          2'b11:
            begin
              west_cfg_bundle  = MUX_NORTH; pe_cfg_bundle   = 2'b11;      end
        endcase


      3'b111: case (east_request_bundle[2:1])
          2'b00:
            begin
              west_cfg_bundle  = MUX_EAST;  south_cfg_bundle = MUX_NORTH; end

          2'b01:
            begin
              west_cfg_bundle  = MUX_EAST;  if (north_request_bundle[2:1] == 2'b11)
                begin
                  south_cfg_bundle  = MUX_PE; pe_cfg_bundle     = 2'b01;  r2pe_ack          = 1'b1;
                end
              else
                  south_cfg_bundle = MUX_NORTH; end
          2'b10:
            begin
              west_cfg_bundle  = MUX_NORTH; if (north_request_bundle[2:1] == 2'b11)
                begin
                  west_cfg_bundle = MUX_PE; pe_cfg_bundle   = 2'b01;  r2pe_ack        = 1'b1;
                end
              else
                south_cfg_bundle = MUX_EAST;  end
          2'b11:
            begin
              if (north_request_bundle[2:1] == 2'b01)
                begin
                  west_cfg_bundle  = MUX_NORTH; south_cfg_bundle = MUX_PE;    end
              else
                begin
                  west_cfg_bundle  = MUX_PE;    south_cfg_bundle = MUX_NORTH;  end
              pe_cfg_bundle   = 2'b11;      r2pe_ack        = 1'b1;
            end
        endcase


    endcase end endmodule
