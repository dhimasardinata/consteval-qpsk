// libraries
#include <algorithm>
#include <array>
#include <cmath>
#include <format>
#include <iostream>
#include <numbers>
#include <print>
#include <ranges>
#include <string>
#include <string_view>
#include <tuple>
#include <vector>

// macros
#define assert static_assert
#define cast static_cast
#define desyncIO                    \
  std::ios::sync_with_stdio(false); \
  std::cin.tie(nullptr)
#define fix static
#define fn void
#define let const
#define lets fix let
#define letx constexpr
#define letsx fix letx
#define letv let var
#define letval consteval
#define letxv letx var
#define spush push_back
#define use using
#define var auto

// namespaces
letxv drop = std::views::drop;
letxv findif = std::ranges::find_if;
letxv rangesize = std::ranges::size;
letxv stride = std::views::stride;
letxv take = std::views::take;
letxv transform = std::views::transform;
letxv zip = std::views::zip;
use error = std::runtime_error;
use std::cerr;
use std::cin;
use std::cos;
use std::cout;
use std::exception;
use std::format;
use std::getline;
use std::pair;
use std::print;
use std::println;
use std::round;
use std::sin;
use std::streamsize;

// data types
use f32 = float;
use i32 = int;
use i16 = short;
use ic8 = char;
use uc8 = unsigned char;
use usz = size_t;
use str = std::string;
use strv = std::string_view;

// constants
letx f32 fc = 10000.0f;
letx f32 fs = 80000.0f;
letx f32 width = 0.001f;
letx usz colw = 10;
letx usz rows = 5;
letx usz sampleperbit = cast<usz>(fs * width);
letx usz lines = sampleperbit / rows;
letxv pi = std::numbers::pi_v<f32>;

// logic check
assert(sampleperbit % rows == 0);

// exact buffer calculation
letval usz bufsize() { return (sampleperbit * colw) + lines; }

// data structures
use arr = std::array<i16, sampleperbit>;
use wavetable = std::array<arr, 4>;
use textbuffer = std::array<ic8, bufsize()>;
use texttable = std::array<textbuffer, 4>;

// comptime bit hacking
letval fn archcheck() { assert('0' == 48 && '1' == 49); }

// comptime lookup table generation (float -> i16)
letval wavetable generatelut() {
  assert(cast<i32>(fc * width) == 10);
  archcheck();
  wavetable table{};
  for (usz i = 0; i < 4; ++i) {
    f32 Iref = (i & 2) ? 1.0f : -1.0f;
    f32 Qref = (i & 1) ? 1.0f : -1.0f;
    for (usz t = 0; t < sampleperbit; ++t) {
      f32 time = cast<f32>(t) / fs;
      f32 rads = 2 * pi * fc * time;
      f32 val = (Iref * cos(rads)) - (Qref * sin(rads));
      table[i][t] = cast<i16>(round(val * 1000.0f));
    }
  }
  return table;
}

// purely functional comptime centering formatter with aligned sign
letval fn fmtcenter(i16 val, ic8* dest) {
  ic8 buf[16]{};
  ic8* end = buf + 16;
  ic8* cur = end;
  bool neg = val < 0;
  i32 absval = neg ? -val : val;
  i32 integerpart = absval / 1000;
  i32 fractpart = absval % 1000;
  for (int k = 0; k < 3; ++k) {
    *--cur = cast<ic8>('0' + (fractpart % 10));
    fractpart /= 10;
  }
  *--cur = '.';
  if (integerpart == 0) {
    *--cur = '0';
  } else {
    while (integerpart > 0) {
      *--cur = cast<ic8>('0' + (integerpart % 10));
      integerpart /= 10;
    }
  }
  usz numlen = cast<usz>(end - cur);
  usz efflen = numlen + 1;
  usz padding = colw > efflen ? colw - efflen : 0;
  usz padleft = padding / 2;
  ic8* out = dest;
  for (usz i = 0; i < padleft; ++i) *out++ = ' ';
  *out++ = neg ? '-' : ' ';
  while (cur < end) *out++ = *cur++;
  while (out < (dest + colw)) *out++ = ' ';
}

// fully comptime string generation
letval texttable precomputestrings() {
  letsx wavetable waves = generatelut();
  texttable txt{};
  for (usz i = 0; i < 4; ++i) {
    ic8* out = txt[i].data();
    for (usz t = 0; t < sampleperbit; ++t) {
      fmtcenter(waves[i][t], out);
      out += colw;
      if ((t + 1) % rows == 0) {
        *out++ = '\n';
      }
    }
  }
  return txt;
}

// comptime lookupvalue
letsx texttable lookuptxt = precomputestrings();

// input function
[[nodiscard]]
str input() {
  print("Bits: ");
  cout.flush();
  str bits;
  if (!getline(cin, bits) || bits.empty())
    throw error("Input failed or empty.");
  letv badit = findif(bits, [](ic8 c) { return (c & 0xFE) != '0'; });
  if (badit != bits.end()) {
    throw error(format("Bits not valid (found '{}').", *badit));
  }
  if (bits.size() & 1) {
    bits.spush('0');
    println("(Padded to even length)");
  }
  return bits;
}

// zero-copy split function using generic ranges
[[nodiscard]]
var splitbits(let str& bits) {
  var I = bits | drop(0) | stride(2);
  var Q = bits | drop(1) | stride(2);
  print("I bits (Len {}): ", rangesize(I));
  for (var c : I | take(10)) print("{}", c);
  if (rangesize(I) > 10) print(" ...");
  print("\n");
  print("Q bits (Len {}): ", rangesize(Q));
  for (var c : Q | take(10)) print("{}", c);
  if (rangesize(Q) > 10) print(" ...");
  print("\n");
  return pair{I, Q};
}

// NRZ encoding preview function
fn nrz(let var& bits, let strv label) {
  print("{} NRZ (Preview): ", label);
  var sig =
      bits | transform([](uc8 c) { return (cast<i32>(c - '0') * 2) - 1; });
  bool first = true;
  for (var val : sig | take(20)) {
    if (!first) print(", ");
    print("{}", val);
    first = false;
  }
  println(" ...");
}

// QPSK modulation function
fn modulatepreview(let var& Isignal, let var& Qsignal) {
  usz totalbit = rangesize(Isignal);
  usz totalsample = totalbit * sampleperbit;
  cout << format("QPSK Streaming Start (Total expected samples: {})\n",
                 totalsample);
  cout << format("{:-<50}\n", "");
  var symbolindices =
      zip(Isignal, Qsignal) | transform([](letv tupleval) {
        letv[Ichar, Qchar] = tupleval;
        return (cast<usz>(Ichar & 1) << 1) | cast<usz>(Qchar & 1);
      });
  letx usz samplelimit = 20;
  usz printed = 0;
  for (usz index : symbolindices) {
    if (printed >= samplelimit) break;
    usz remaining = samplelimit - printed;
    if (remaining >= sampleperbit) {
      cout.write(lookuptxt[index].data(), cast<streamsize>(bufsize()));
      printed += sampleperbit;
    } else {
      usz fulllines = remaining / rows;
      usz partialcols = remaining % rows;
      usz bytestocopy =
          (fulllines * ((colw * rows) + 1)) + (partialcols * colw);
      cout.write(lookuptxt[index].data(), cast<streamsize>(bytestocopy));
      printed += remaining;
    }
  }
  if (printed % rows != 0) cout << '\n';
  cout.flush();
  if (totalsample > samplelimit) {
    cout << format("{:^50}\n", format("... ({} samples hidden) ...",
                                      totalsample - printed));
  }
  cout << format("{:-<50}\n", "");
  cout << format("Stream Complete. Processed {} samples.\n", totalsample);
}

// main function
i32 main() {
  desyncIO;
  try {
    str bits = input();
    letv[Iview, Qview] = splitbits(bits);
    nrz(Iview, "I-channel");
    nrz(Qview, "Q-channel");
    modulatepreview(Iview, Qview);
  } catch (let exception& e) {
    println(cerr, "Error: {}", e.what());
    return 1;
  }
  return 0;
}