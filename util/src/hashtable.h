/* Copyright (C) 2011 Aigui Liu
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, visit the http://fsf.org website.
 */

#ifndef _HASHTABLE_H
#define _HASHTABLE_H

#include <string.h>

#ifndef __USE_ISOC99
#define inline
#endif

#define create_hashtable(hsize) \
         hash_create(lh_strhash, equal_str, hsize)

unsigned int lh_strhash(void *src);
int equal_str(void *k1, void *k2);

struct hashentry;
struct _hashtable;
typedef struct _hashtable   hashtable;


hashtable *hash_create(unsigned int (*keyfunc)(void *),
                       int (*comparefunc)(void *,void *),
                       int size);
void hash_free(hashtable *tab);
void hash_insert(void *key, void *data, hashtable *tab);
void hash_remove(void *key, hashtable *tab);
void *hash_value(void *key, hashtable *tab);
void hash_for_each_do(hashtable *tab, int (cb)(void *, void *));
int hash_count(hashtable *tab);

#endif

