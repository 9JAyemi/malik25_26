// Add inside elastic1632 (or bind to it). Focused, concise SVA.

`ifdef SVA

// local init flags for $past safety
logic winit, rinit;
always @(posedge wclk) winit <= 1'b1;
always @(posedge rclk) rinit <= 1'b1;

// 1) ALIGN primitive detection (both directions)
assert property (@(posedge wclk)
  ({data_in, data_in_r}==ALIGN_PRIM &&
   {charisk_in, charisk_in_r}==4'h1 &&
   {notintable_in, notintable_in_r}==4'h0 &&
   {disperror_in,  disperror_in_r}==4'h0) |-> is_alignp_w);

assert property (@(posedge wclk)
  is_alignp_w |->
  ({data_in, data_in_r}==ALIGN_PRIM &&
   {charisk_in, charisk_in_r}==4'h1 &&
   {notintable_in, notintable_in_r}==4'h0 &&
   {disperror_in,  disperror_in_r}==4'h0));

// 2) wclk-domain state updates
assert property (@(posedge wclk) winit |-> aligned32_in_r ==
  (!$past(isaligned_in) ? 1'b0 :
   ($past(is_alignp_w)  ? 1'b1 : $past(aligned32_in_r))));

assert property (@(posedge wclk) winit |-> msb_in_r ==
  ((!$past(aligned32_in_r) && !$past(is_alignp_w)) ? 1'b1 : !$past(msb_in_r)));

assert property (@(posedge wclk) winit |-> inc_waddr ==
  (!$past(msb_in_r) || ($past(is_alignp_w) && !$past(aligned32_in_r))));

assert property (@(posedge wclk) winit |-> waddr ==
  (!$past(aligned32_in_r) ? '0 :
   ($past(inc_waddr) ? ($past(waddr)+1'b1) : $past(waddr))));

assert property (@(posedge wclk) winit |-> fill ==
  (!$past(aligned32_in_r) ? '0 :
   ($past(msb_in_r) ? { $past(fill[FIFO_DEPTH-2:0]), ~$past(waddr[DEPTH_LOG2]) }
                    :  $past(fill))));

// 3) rclk-domain combinational/pipe equivalences
assert property (@(posedge rclk) raddr_w ==
  (aligned_rclk[1] ? ( raddr_r +
     (add_rclk_r[0] ? SIZED0
                    : (skip_rclk ? (skip_rclk2 ? SIZED3 : SIZED2) : SIZED1)))
                   : SIZED0));

assert property (@(posedge rclk) rinit |-> raddr_r == $past(raddr_w));

// 4) Skip/correct logic
assert property (@(posedge rclk) skip_rclk  == (correct &&      dav_rclk[1]));
assert property (@(posedge rclk) skip_rclk2 == (correct_first && dav_rclk_more[1]));

assert property (@(posedge rclk) correct_stream == (align_out && pre_align_out_r && !correct_r[2]));
assert property (@(posedge rclk) correct_first  == (pre_align_out_r && !align_out));
assert property (@(posedge rclk) correct        == (correct_stream || correct_first));

assert property (@(posedge rclk) rinit |-> correct_r ==
  (($past(correct) || !$past(|aligned_rclk)) ? '1 : ($past(correct_r) << 1)));

assert property (@(posedge rclk) rinit |-> add_rclk_r ==
  ($past(correct_first)  ? {~$past(dav_rclk_less[1]), ~$past(dav_rclk[1])} :
   ($past(correct_stream) ? {1'b0,                     ~$past(dav_rclk[1])} :
                            ($past(add_rclk_r) >> 1))));

// 5) Outputs and flags
assert property (@(posedge rclk) isaligned_out == aligned_rclk[2]);

assert property (@(posedge rclk) full  == ((|aligned_rclk) &&  full_1[1] && !full_0[1]));
assert property (@(posedge rclk) empty == ((|aligned_rclk) && !full_1[1] &&  full_0[1]));
assert property (@(posedge rclk) !(full && empty));

assert property (@(posedge rclk) (!|aligned_rclk) |-> (!full && !empty));

assert property (@(posedge rclk) rinit |-> disperror_out  == $past(rdata_r[43:40]));
assert property (@(posedge rclk) rinit |-> notintable_out == $past(rdata_r[39:36]));
assert property (@(posedge rclk) rinit |-> charisk_out    == $past(rdata_r[35:32]));
assert property (@(posedge rclk) rinit |-> data_out       == $past(rdata_r[31:0]));

// 6) Reset-like behavior on rclk when write-side not aligned
assert property (@(posedge rclk) !aligned32_in_r |=> !|aligned_rclk);
assert property (@(posedge rclk) !aligned32_in_r |=> dav_rclk==2'b00 && dav_rclk_more==2'b00 && dav_rclk_less==2'b00);

// 7) Key coverage
cover property (@(posedge wclk) !aligned32_in_r ##1 (isaligned_in && is_alignp_w) ##1 aligned32_in_r);
cover property (@(posedge wclk) aligned32_in_r && msb_in_r);
cover property (@(posedge rclk) isaligned_out && correct_first  && dav_rclk_more[1] && skip_rclk2);
cover property (@(posedge rclk) isaligned_out && correct_stream && dav_rclk[1]      && skip_rclk);
cover property (@(posedge rclk) $rose(full));
cover property (@(posedge rclk) $rose(empty));

`endif