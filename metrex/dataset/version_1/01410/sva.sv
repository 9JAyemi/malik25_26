// SVA for LCD. Bind into the DUT for internal signal visibility.
module LCD_sva;

  // Default clocking
  default clocking cb @(posedge clk); endclocking

  // ---------- Sanity ----------
  // State in legal range
  assert property (state inside {
      f_rst,f_idle,f_reset,f_set,f_clear,f_off,f_on,f_entry,f_cursor,f_w_char,
      res_data,set_data,clear_data,off_data,on_data,entry_data,cursor_data,write_data,
      lcd_en,lcd_del_1,lcd_dis,lcd_del_200});

  // No X on critical controls
  assert property (!$isunknown({state,busy,e,rs,en_cnt}));

  // ---------- Reset / idle control ----------
  // Sync reset drives state to f_rst next cycle
  assert property (rst |=> state==f_rst);
  // Exit f_rst to idle
  assert property (disable iff (rst) state==f_rst |=> state==f_idle);
  // Idle holds without en
  assert property (disable iff (rst) state==f_idle && !en |=> state==f_idle);

  // Priority decode from idle when en
  assert property (disable iff (rst) state==f_idle && en && reset |=> state==f_reset);
  assert property (disable iff (rst) state==f_idle && en && !reset && set |=> state==f_set);
  assert property (disable iff (rst) state==f_idle && en && !reset && !set && clear |=> state==f_clear);
  assert property (disable iff (rst) state==f_idle && en && !reset && !set && !clear && off |=> state==f_off);
  assert property (disable iff (rst) state==f_idle && en && !(reset||set||clear||off) && on |=> state==f_on);
  assert property (disable iff (rst) state==f_idle && en && !(reset||set||clear||off||on) && entry_mode |=> state==f_entry);
  assert property (disable iff (rst) state==f_idle && en && !(reset||set||clear||off||on||entry_mode) && cursor |=> state==f_cursor);
  assert property (disable iff (rst) state==f_idle && en && !(reset||set||clear||off||on||entry_mode||cursor) && w_char |=> state==f_w_char);
  // If en but no request, stay idle
  assert property (disable iff (rst) state==f_idle && en && !(reset||set||clear||off||on||entry_mode||cursor||w_char) |=> state==f_idle);

  // ---------- One-step transitions into common send/hold pipeline ----------
  assert property (disable iff (rst) state==f_reset    |=> state==res_data   ##1 state==lcd_en);
  assert property (disable iff (rst) state==f_set      |=> state==set_data   ##1 state==lcd_en);
  assert property (disable iff (rst) state==f_clear    |=> state==clear_data ##1 state==lcd_en);
  assert property (disable iff (rst) state==f_off      |=> state==off_data   ##1 state==lcd_en);
  assert property (disable iff (rst) state==f_on       |=> state==on_data    ##1 state==lcd_en);
  assert property (disable iff (rst) state==f_entry    |=> state==entry_data ##1 state==lcd_en);
  assert property (disable iff (rst) state==f_cursor   |=> state==cursor_data##1 state==lcd_en);
  assert property (disable iff (rst) state==f_w_char   |=> state==write_data ##1 state==lcd_en);

  // ---------- Handshake pipeline control ----------
  assert property (disable iff (rst) state==lcd_en   |=> state==lcd_del_1);
  assert property (disable iff (rst) state==lcd_del_1 && !int_cnt |=> state==lcd_del_1);
  assert property (disable iff (rst) state==lcd_del_1 &&  int_cnt |=> state==lcd_dis);
  assert property (disable iff (rst) state==lcd_dis  |=> state==lcd_del_200);
  assert property (disable iff (rst) state==lcd_del_200 && !int_cnt |=> state==lcd_del_200);
  assert property (disable iff (rst) state==lcd_del_200 &&  int_cnt |=> state==f_idle);

  // ---------- Output encodings per state ----------
  // Busy only low in idle
  assert property (disable iff (rst) (state==f_idle) |-> !busy);
  assert property (disable iff (rst) (state!=f_idle) |->  busy);

  // e high only in lcd_en/lcd_del_1
  assert property (disable iff (rst) e == (state==lcd_en || state==lcd_del_1));

  // en_cnt high only in delay states
  assert property (disable iff (rst) en_cnt == (state==lcd_del_1 || state==lcd_del_200));

  // limit_cnt values
  assert property (disable iff (rst) (state==lcd_en || state==lcd_del_1)  |-> limit_cnt==16'd100);
  assert property (disable iff (rst) (state==lcd_dis || state==lcd_del_200)|-> limit_cnt==16'd20000);
  assert property (disable iff (rst)
    (state inside {f_rst,f_idle,f_reset,f_set,f_clear,f_off,f_on,f_entry,f_cursor,f_w_char,
                   res_data,set_data,clear_data,off_data,on_data,entry_data,cursor_data,write_data})
    |-> limit_cnt==16'd0);

  // Data/RS encodings in data-setup states
  assert property (disable iff (rst) state==res_data    |-> rs==0 && e==0 && data==8'h30);
  assert property (disable iff (rst) state==set_data    |-> rs==0 && e==0 && data==8'h38);
  assert property (disable iff (rst) state==clear_data  |-> rs==0 && e==0 && data==8'h01);
  assert property (disable iff (rst) state==off_data    |-> rs==0 && e==0 && data==8'h08);
  assert property (disable iff (rst) state==on_data     |-> rs==0 && e==0 && data==8'h0C);
  assert property (disable iff (rst) state==entry_data  |-> rs==0 && e==0 && data==8'h06);
  assert property (disable iff (rst) state==cursor_data |-> rs==0 && e==0 && data==(8'h80 | cursor_pos));
  assert property (disable iff (rst) state==write_data  |-> rs==1 && e==0 && data==ascii_char);

  // Pre-data command states
  assert property (disable iff (rst)
    (state inside {f_reset,f_set,f_clear,f_off,f_on,f_entry,f_cursor}) |-> rs==0 && e==0 && data==8'h00);
  assert property (disable iff (rst) state==f_w_char |-> rs==1 && e==0 && data==8'h00);

  // Payload held stable throughout handshake window
  assert property (disable iff (rst)
    (state inside {lcd_en,lcd_del_1,lcd_dis,lcd_del_200}) |-> $stable({rs,data}));

  // In handshake states, drive from latched copies
  assert property (disable iff (rst)
    (state inside {lcd_en,lcd_del_1,lcd_dis,lcd_del_200}) |-> (rs==rs_d && data==data_d));

  // ---------- Coverage ----------
  // Cover each command’s full path back to idle (with both int_cnt pulses)
  cover property (disable iff (rst)
    state==f_reset ##1 res_data ##1 lcd_en ##1
    (state==lcd_del_1, !int_cnt)[*1:$] ##1 (state==lcd_del_1 && int_cnt) ##1
    lcd_dis ##1 lcd_del_200 ##1
    (state==lcd_del_200, !int_cnt)[*1:$] ##1 (state==lcd_del_200 && int_cnt) ##1
    f_idle);

  cover property (disable iff (rst) state==f_set     ##1 set_data     ##1 lcd_en ##1 f_idle [->1]);
  cover property (disable iff (rst) state==f_clear   ##1 clear_data   ##1 lcd_en ##1 f_idle [->1]);
  cover property (disable iff (rst) state==f_off     ##1 off_data     ##1 lcd_en ##1 f_idle [->1]);
  cover property (disable iff (rst) state==f_on      ##1 on_data      ##1 lcd_en ##1 f_idle [->1]);
  cover property (disable iff (rst) state==f_entry   ##1 entry_data   ##1 lcd_en ##1 f_idle [->1]);
  cover property (disable iff (rst) state==f_cursor  ##1 cursor_data  ##1 lcd_en ##1 f_idle [->1]);
  cover property (disable iff (rst) state==f_w_char  ##1 write_data   ##1 lcd_en ##1 f_idle [->1]);

  // Hit every state at least once
  cover property (state inside {
      f_rst,f_idle,f_reset,f_set,f_clear,f_off,f_on,f_entry,f_cursor,f_w_char,
      res_data,set_data,clear_data,off_data,on_data,entry_data,cursor_data,write_data,
      lcd_en,lcd_del_1,lcd_dis,lcd_del_200});

endmodule

// Bind into all LCD instances
bind LCD LCD_sva lcd_sva_i();