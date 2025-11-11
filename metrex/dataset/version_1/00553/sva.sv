// SVA for segDisplayDriver
// Bind these assertions to the DUT

module segDisplayDriver_sva #(
  parameter int unsigned DIV = 32'd200_000
)(
  input logic               clk,
  input logic               clk_500Hz,
  input logic [31:0]        clk_cnt,

  input logic [15:0]        data,
  input logic [3:0]         out_dig,
  input logic [7:0]         out_seg,

  // internal DUT regs (for binding)
  input logic [3:0]         dig_ctrl,
  input logic [4:0]         seg_ctrl,
  input logic [7:0]         seg_reg
);

  // 7-seg decode expected for nibbles 0..F
  function automatic logic [7:0] seg7(input logic [3:0] n);
    case (n)
      4'h0:  seg7 = 8'b1100_0000;
      4'h1:  seg7 = 8'b1111_1001;
      4'h2:  seg7 = 8'b1010_0100;
      4'h3:  seg7 = 8'b1011_0000;
      4'h4:  seg7 = 8'b1001_1001;
      4'h5:  seg7 = 8'b1001_0010;
      4'h6:  seg7 = 8'b1000_0010;
      4'h7:  seg7 = 8'b1111_1000;
      4'h8:  seg7 = 8'b1000_0000;
      4'h9:  seg7 = 8'b1001_0000;
      4'hA:  seg7 = 8'b1000_1000;
      4'hB:  seg7 = 8'b1000_0011;
      4'hC:  seg7 = 8'b1100_0110;
      4'hD:  seg7 = 8'b1010_0001;
      4'hE:  seg7 = 8'b1000_0110;
      4'hF:  seg7 = 8'b1000_1110;
      default: seg7 = 8'hFF;
    endcase
  endfunction

  // Select the nibble based on active-low digit
  function automatic logic [3:0] sel_nib(input logic [3:0] od, input logic [15:0] d);
    case (od)
      4'b1110: sel_nib = d[3:0];
      4'b1101: sel_nib = d[7:4];
      4'b1011: sel_nib = d[11:8];
      4'b0111: sel_nib = d[15:12];
      default: sel_nib = 4'hx;
    endcase
  endfunction

  // Clock divider and toggle behavior
  assert property (@(posedge clk)
    !$isunknown($past(clk_cnt)) && $past(clk_cnt) < DIV |-> clk_cnt == $past(clk_cnt)+1
  );

  assert property (@(posedge clk)
    !$isunknown($past(clk_cnt)) && $past(clk_cnt) == DIV |-> (clk_cnt == 0) && (clk_500Hz == !$past(clk_500Hz))
  );

  assert property (@(posedge clk)
    (clk_500Hz ^ $past(clk_500Hz)) |-> $past(clk_cnt) == DIV
  );

  assert property (@(posedge clk)
    ! $isunknown(clk_cnt) |-> clk_cnt <= DIV
  );

  // out_dig reflects internal reg continuously
  assert property (@(posedge clk) out_dig == dig_ctrl);
  // out_seg reflects internal reg continuously
  assert property (@(posedge clk) out_seg == seg_reg);

  // Digit control: one-hot-low rotation at clk_500Hz edge
  assert property (@(posedge clk_500Hz)
    1'b1 |-> ##0 out_dig == { $past(out_dig)[2:0], $past(out_dig)[3] }
  );

  assert property (@(posedge clk_500Hz)
    ##0 out_dig inside {4'b1110,4'b1101,4'b1011,4'b0111}
  );

  // Digit control stable between clk_500Hz edges (sampled on faster clk)
  assert property (@(posedge clk)
    !$rose(clk_500Hz) |-> $stable(out_dig)
  );

  // seg_ctrl must mirror selected nibble (MSB=0) at update
  assert property (@(posedge clk_500Hz)
    1'b1 |-> ##0 (seg_ctrl[4] == 1'b0) && (seg_ctrl[3:0] == sel_nib(out_dig, data))
  );

  // Default seg_ctrl value (5'h1f) should never be used
  assert property (@(posedge clk_500Hz)
    1'b1 |-> ##0 seg_ctrl != 5'h1F
  );

  // Segment output must decode selected nibble
  assert property (@(posedge clk_500Hz)
    1'b1 |-> ##0 out_seg == seg7(sel_nib(out_dig, data))
  );

  // If data is stable and no digit edge, segments must be stable
  assert property (@(posedge clk)
    !$rose(clk_500Hz) && $stable(data) |-> $stable(out_seg)
  );

  // Coverage
  cover property (@(posedge clk_500Hz)
    out_dig==4'b1110 ##1 out_dig==4'b1101 ##1 out_dig==4'b1011 ##1 out_dig==4'b0111 ##1 out_dig==4'b1110
  );

  cover property (@(posedge clk) $rose(clk_500Hz));

  // Cover all hex patterns observed on the active digit
  genvar i;
  generate
    for (i=0; i<16; i++) begin : C_HEX
      cover property (@(posedge clk_500Hz)
        1'b1 |-> ##0 (sel_nib(out_dig, data) == i[3:0]) && (out_seg == seg7(i[3:0]))
      );
    end
  endgenerate

endmodule

bind segDisplayDriver segDisplayDriver_sva #(.DIV(32'd200_000)) segDisplayDriver_sva_i (
  .clk(clk),
  .clk_500Hz(clk_500Hz),
  .clk_cnt(clk_cnt),
  .data(data),
  .out_dig(out_dig),
  .out_seg(out_seg),
  .dig_ctrl(dig_ctrl),
  .seg_ctrl(seg_ctrl),
  .seg_reg(seg_reg)
);