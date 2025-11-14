// SVA checker for bridge: bind this to the DUT
module bridge_sva (
  input  logic        f_signed_i,
  input  logic [1:0]  f_siz_i,
  input  logic [2:0]  f_adr_i,
  input  logic [63:0] f_dat_i,
  input  logic [63:0] wb_dat_i,
  input  logic [63:0] f_dat_o,
  input  logic [63:0] wb_dat_o,
  input  logic [7:0]  wb_sel_o
);

  function automatic [7:0] sel_mask(input logic [1:0] size, input logic [2:0] adr);
    unique case (size)
      2'b11: sel_mask = 8'hFF;
      2'b10: sel_mask = adr[2] ? 8'hF0 : 8'h0F;
      2'b01: sel_mask = 8'h03 << (adr[2:1]*2);
      2'b00: sel_mask = 8'h01 << adr[2:0];
      default: sel_mask = '0;
    endcase
  endfunction

  function automatic [63:0] rep_wdata(input logic [1:0] size, input logic [63:0] din);
    unique case (size)
      2'b11: rep_wdata = din;
      2'b10: rep_wdata = {2{din[31:0]}};
      2'b01: rep_wdata = {4{din[15:0]}};
      2'b00: rep_wdata = {8{din[7:0]}};
      default: rep_wdata = '0;
    endcase
  endfunction

  function automatic [63:0] exp_rdata(
      input logic [1:0] size, input logic [2:0] adr, input logic sgn, input logic [63:0] wbi);
    logic [31:0] w32; logic [15:0] w16; logic [7:0] w8; logic [63:0] out;
    unique case (size)
      2'b11: out = wbi;
      2'b10: begin
        w32 = adr[2] ? wbi[63:32] : wbi[31:0];
        out = sgn ? {{32{w32[31]}}, w32} : {32'h0, w32};
      end
      2'b01: begin
        unique case (adr[2:1])
          2'b00: w16 = wbi[15:0];
          2'b01: w16 = wbi[31:16];
          2'b10: w16 = wbi[47:32];
          2'b11: w16 = wbi[63:48];
        endcase
        out = sgn ? {{48{w16[15]}}, w16} : {48'h0, w16};
      end
      2'b00: begin
        unique case (adr[2:0])
          3'd0: w8 = wbi[7:0];
          3'd1: w8 = wbi[15:8];
          3'd2: w8 = wbi[23:16];
          3'd3: w8 = wbi[31:24];
          3'd4: w8 = wbi[39:32];
          3'd5: w8 = wbi[47:40];
          3'd6: w8 = wbi[55:48];
          3'd7: w8 = wbi[63:56];
        endcase
        out = sgn ? {{56{w8[7]}}, w8} : {56'h0, w8};
      end
      default: out = '0;
    endcase
    return out;
  endfunction

  // Core checks (combinational)
  always_comb begin
    // Control integrity
    assert (!$isunknown({f_siz_i, f_signed_i, f_adr_i}))
      else $error("bridge: X/Z on control inputs");

    // Byte select mask matches size/address decode
    assert (wb_sel_o == sel_mask(f_siz_i, f_adr_i))
      else $error("bridge: wb_sel_o mismatch");

    // Write data replication/packing
    assert (wb_dat_o == rep_wdata(f_siz_i, f_dat_i))
      else $error("bridge: wb_dat_o packing mismatch");

    // Read data extraction + sign/zero extend
    assert (f_dat_o == exp_rdata(f_siz_i, f_adr_i, f_signed_i, wb_dat_i))
      else $error("bridge: f_dat_o unpack/extend mismatch");

    // Coverage: all sizes and address positions
    cover (f_siz_i == 2'b11);

    cover (f_siz_i == 2'b10 && f_adr_i[2]==1'b0);
    cover (f_siz_i == 2'b10 && f_adr_i[2]==1'b1);

    cover (f_siz_i == 2'b01 && f_adr_i[2:1]==2'b00);
    cover (f_siz_i == 2'b01 && f_adr_i[2:1]==2'b01);
    cover (f_siz_i == 2'b01 && f_adr_i[2:1]==2'b10);
    cover (f_siz_i == 2'b01 && f_adr_i[2:1]==2'b11);

    cover (f_siz_i == 2'b00 && f_adr_i[2:0]==3'd0);
    cover (f_siz_i == 2'b00 && f_adr_i[2:0]==3'd1);
    cover (f_siz_i == 2'b00 && f_adr_i[2:0]==3'd2);
    cover (f_siz_i == 2'b00 && f_adr_i[2:0]==3'd3);
    cover (f_siz_i == 2'b00 && f_adr_i[2:0]==3'd4);
    cover (f_siz_i == 2'b00 && f_adr_i[2:0]==3'd5);
    cover (f_siz_i == 2'b00 && f_adr_i[2:0]==3'd6);
    cover (f_siz_i == 2'b00 && f_adr_i[2:0]==3'd7);

    // Coverage: sign extension (pos/neg) for sub-dword loads
    logic [31:0] sel32 = f_adr_i[2] ? wb_dat_i[63:32] : wb_dat_i[31:0];
    logic [15:0] sel16 = (f_adr_i[2:1]==2'b00) ? wb_dat_i[15:0]  :
                         (f_adr_i[2:1]==2'b01) ? wb_dat_i[31:16] :
                         (f_adr_i[2:1]==2'b10) ? wb_dat_i[47:32] : wb_dat_i[63:48];
    logic [7:0]  sel8;
    unique case (f_adr_i[2:0])
      3'd0: sel8 = wb_dat_i[7:0];
      3'd1: sel8 = wb_dat_i[15:8];
      3'd2: sel8 = wb_dat_i[23:16];
      3'd3: sel8 = wb_dat_i[31:24];
      3'd4: sel8 = wb_dat_i[39:32];
      3'd5: sel8 = wb_dat_i[47:40];
      3'd6: sel8 = wb_dat_i[55:48];
      3'd7: sel8 = wb_dat_i[63:56];
    endcase

    cover (f_siz_i==2'b10 && f_signed_i &&  sel32[31]);
    cover (f_siz_i==2'b10 && f_signed_i && !sel32[31]);
    cover (f_siz_i==2'b01 && f_signed_i &&  sel16[15]);
    cover (f_siz_i==2'b01 && f_signed_i && !sel16[15]);
    cover (f_siz_i==2'b00 && f_signed_i &&  sel8[7]);
    cover (f_siz_i==2'b00 && f_signed_i && !sel8[7]);
  end

endmodule

bind bridge bridge_sva bridge_sva_i (
  .f_signed_i(f_signed_i),
  .f_siz_i   (f_siz_i),
  .f_adr_i   (f_adr_i),
  .f_dat_i   (f_dat_i),
  .wb_dat_i  (wb_dat_i),
  .f_dat_o   (f_dat_o),
  .wb_dat_o  (wb_dat_o),
  .wb_sel_o  (wb_sel_o)
);