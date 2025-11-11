// SVA for adbg_crc32
// Bind this module to adbg_crc32 to check/cover key behavior
module adbg_crc32_sva (
  input         clk,
  input         data,
  input         enable,
  input         shift,
  input         clr,
  input         rst,
  input  [31:0] crc_out,
  input         serial_out,
  input  [31:0] crc,
  input  [31:0] new_crc
);

  function automatic [31:0] exp_new_crc(input [31:0] c, input bit d);
    exp_new_crc[0]  = c[1];
    exp_new_crc[1]  = c[2];
    exp_new_crc[2]  = c[3];
    exp_new_crc[3]  = c[4];
    exp_new_crc[4]  = c[5];
    exp_new_crc[5]  = c[6] ^ d ^ c[0];
    exp_new_crc[6]  = c[7];
    exp_new_crc[7]  = c[8];
    exp_new_crc[8]  = c[9]  ^ d ^ c[0];
    exp_new_crc[9]  = c[10] ^ d ^ c[0];
    exp_new_crc[10] = c[11];
    exp_new_crc[11] = c[12];
    exp_new_crc[12] = c[13];
    exp_new_crc[13] = c[14];
    exp_new_crc[14] = c[15];
    exp_new_crc[15] = c[16] ^ d ^ c[0];
    exp_new_crc[16] = c[17];
    exp_new_crc[17] = c[18];
    exp_new_crc[18] = c[19];
    exp_new_crc[19] = c[20] ^ d ^ c[0];
    exp_new_crc[20] = c[21] ^ d ^ c[0];
    exp_new_crc[21] = c[22] ^ d ^ c[0];
    exp_new_crc[22] = c[23];
    exp_new_crc[23] = c[24] ^ d ^ c[0];
    exp_new_crc[24] = c[25] ^ d ^ c[0];
    exp_new_crc[25] = c[26];
    exp_new_crc[26] = c[27] ^ d ^ c[0];
    exp_new_crc[27] = c[28] ^ d ^ c[0];
    exp_new_crc[28] = c[29];
    exp_new_crc[29] = c[30] ^ d ^ c[0];
    exp_new_crc[30] = c[31] ^ d ^ c[0];
    exp_new_crc[31] =          d ^ c[0];
  endfunction

  // Async reset takes effect immediately on rst posedge
  assert property (@(posedge rst) 1 |-> crc == 32'hffff_ffff)
    else $error("crc not all-ones at rst posedge");

  // While rst held, crc must be all-ones at each clk
  assert property (@(posedge clk) rst |-> crc == 32'hffff_ffff)
    else $error("crc not held all-ones while rst asserted");

  // clr has synchronous highest priority after rst
  assert property (@(posedge clk) disable iff (rst)
                   clr |-> crc == 32'hffff_ffff)
    else $error("clr did not load all-ones");

  // When enable (and not clr), crc updates with polynomial
  assert property (@(posedge clk) disable iff (rst)
                   (!clr && enable) |=> crc == exp_new_crc($past(crc), $past(data)))
    else $error("enable update mismatch");

  // When shift (and not clr/enable), crc shifts right with zero MSB insert
  assert property (@(posedge clk) disable iff (rst)
                   (!clr && !enable && shift) |=> crc == {1'b0, $past(crc[31:1])})
    else $error("shift update mismatch");

  // When no control, crc holds
  assert property (@(posedge clk) disable iff (rst)
                   (!clr && !enable && !shift) |=> crc == $past(crc))
    else $error("crc not held when idle");

  // Enable has priority over shift (redundant with enable property but explicit)
  assert property (@(posedge clk) disable iff (rst)
                   (!clr && enable && shift) |=> crc == exp_new_crc($past(crc), $past(data)))
    else $error("enable did not take priority over shift");

  // Combinational new_crc wiring matches polynomial
  assert property (@(posedge clk) new_crc == exp_new_crc(crc, data))
    else $error("new_crc combinational function incorrect");

  // Outputs reflect internal crc
  assert property (@(posedge clk) (crc_out == crc) && (serial_out == crc[0]))
    else $error("Outputs not driven correctly from crc");

  // No X/Z on key state/outputs after reset release
  assert property (@(posedge clk) disable iff (rst)
                   !$isunknown(crc) && !$isunknown(crc_out) && !$isunknown(serial_out))
    else $error("X/Z detected on crc/crc_out/serial_out");

  // Coverage
  cover property (@(posedge rst) 1);                                   // async reset seen
  cover property (@(posedge clk) disable iff (rst) clr);               // clr seen
  cover property (@(posedge clk) disable iff (rst) enable && (data==0));
  cover property (@(posedge clk) disable iff (rst) enable && (data==1));
  cover property (@(posedge clk) disable iff (rst) shift);             // shift seen
  cover property (@(posedge clk) disable iff (rst) enable && shift);   // simultaneous enable+shift
  cover property (@(posedge clk) disable iff (rst) serial_out != $past(serial_out)); // serial_out toggles

endmodule

// Example bind (place in a testbench or bind file):
// bind adbg_crc32 adbg_crc32_sva u_adbg_crc32_sva (
//   .clk(clk), .data(data), .enable(enable), .shift(shift), .clr(clr), .rst(rst),
//   .crc_out(crc_out), .serial_out(serial_out), .crc(crc), .new_crc(new_crc)
// );