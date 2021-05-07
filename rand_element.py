#!/bin/python

from random import *

def rand_card():
    colors = ["red", "yellow", "green", "blue"]
    shuffle(colors)

    number = randint(1, 13)

    if randint(0, 100) <= 2:
        return "joker"
    else:
        return f"{colors[0]} {number}"

cards = {}

def contains_max_amount_of_card(cards, card):
    if card == "joker":
        return cards.get(card, 0) == 4
    else:
        return cards.get(card, 0) == 2

for i in range(1, 15):
    card = rand_card()
    while contains_max_amount_of_card(cards, card):
        card = rand_card()

    cards[card] = cards.get(card, 0) + 1

result = []
for k, v in cards.items():
    for i in range(0, v):
        result.append(k)

result.sort()

for i in result:
    print(i)

